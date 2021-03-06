open CCResult.Infix
open Rresult

(*As seen in jsonm documentation*)
type json =
  [ `Null
  | `Bool of bool
  | `Float of float
  | `String of string
  | `A of json list
  | `O of (string * json) list ]

let assert_r test msg =
  if test then Ok () else
    R.error_msg @@ "Assertion '"^msg^"' failed"

let catch_r f x ~msg = try Ok (f x) with _ -> R.error_msg msg

module Bits = struct

  type t = Char.t
  
  let take_left n byte =
    assert (n >= 0 && n <= 8);
    let c = byte |> Char.code in
    c lsr (8-n)
    |> Char.chr

  let drop_left n byte =
    assert (n >= 0 && n <= 8);
    let c = byte |> Char.code in
    (((c lsl n) land 0b1111_1111) lsr n)
    |> Char.chr

  let get i byte =
    assert (i >= 0 && i < 8);
    let c = byte |> Char.code in
    match i with
    | 0 -> c land 0b1000_0000
    | 1 -> c land 0b0100_0000
    | 2 -> c land 0b0010_0000
    | 3 -> c land 0b0001_0000
    | 4 -> c land 0b0000_1000
    | 5 -> c land 0b0000_0100
    | 6 -> c land 0b0000_0010
    | 7 -> c land 0b0000_0001
    | _ -> failwith "Will not happen"

  let explode_byte byte = List.init 8 (fun i -> get i byte)
  
end

module ByteStream = struct

  type string_stream = {
    string : string;
    mutable offset : int;
  }
  
  type t = [ `Channel of in_channel | `StringStream of string_stream ]

  let take : int -> t -> (string, _) result =
    fun n -> function
      | `Channel channel -> (
          match really_input_string channel n with
          | exception End_of_file ->
            R.error_msg "End of stream"
          | s -> Ok s
        )
      | `StringStream stream ->
        if stream.offset + n > String.length stream.string then
          R.error_msg "End of stream"
        else
          let chunk = String.sub stream.string stream.offset n in
          stream.offset <- stream.offset + n;
          Ok chunk

  let of_string string = `StringStream {
    string;
    offset = 0;
  }

  let of_channel channel = `Channel channel 

  type source = [ `Channel of in_channel | `String of string ]
  
  let of_source : source -> t = function 
    | `Channel channel -> of_channel channel
    | `String string -> of_string string

end

module Jsonr = struct 

  module Bin = struct

    module type IntAbstract = sig

      type t

      module Infix : sig
        val (lsl) : t -> int -> t
        val (lor) : t -> t -> t
      end

    end
    
    (*goto possibly check for integer overflow*)
    let int_of_byte_string_aux :
      type int_abstract.
        (module IntAbstract with type t = int_abstract)
      -> of_int:(int -> int_abstract)
      -> drop_bits_left:int
      -> string
      -> int_abstract
      = fun int_module ~of_int ~drop_bits_left byte_string ->
        let module IntAbstract =
          (val int_module : IntAbstract with type t = int_abstract) in
        let byte_length = 8 in
        byte_string
        |> CCString.fold (fun (acc_int, drop_bits_left) byte ->
          if drop_bits_left >= byte_length then
            (acc_int, drop_bits_left - byte_length)
          else
            let drop_bits_now = min byte_length drop_bits_left in
            let filtered_byte = byte |> Bits.drop_left drop_bits_now in
            let acc_int = IntAbstract.Infix.(
              (acc_int lsl byte_length) lor (of_int (Char.code filtered_byte))
            )
            in
            (acc_int, drop_bits_left - drop_bits_now)
        ) (of_int 0, drop_bits_left)
        |> fun (result, _) -> result

    let int_of_byte_string = int_of_byte_string_aux (module CCInt) ~of_int:CCFun.id
    let int_of_byte b ~drop_bits_left =
      b |> CCString.of_char |> int_of_byte_string ~drop_bits_left
    let int32_of_byte_string = int_of_byte_string_aux (module CCInt32) ~of_int:CCInt32.of_int
    let int64_of_byte_string = int_of_byte_string_aux (module CCInt64) ~of_int:CCInt64.of_int
    
    let string_of_byte_array bs = bs |> Array.map Char.chr |> CCString.of_array

    let char_of_string s =
      assert (String.length s = 1);
      s.[0]

    (* let int_of_byte_array ~drop_bits_left bytes =
     *   bytes
     *   |> CCString.of_array
     *   |> int_of_byte_string (module CCInt) ~of_int:CCFun.id ~drop_bits_left *)

    let magic_number =
      [| 0b11010011; 0b01001010; 0b01010010; 0b01100010 |]
      |> string_of_byte_array

    let version =
      [| 0b00000001 |] 
      |> string_of_byte_array

    module Dictionary = struct

      let make_static ~size = function
        | None ->
          assert_r (size = 0) "Static dictionary: Wrong size" >|= fun () ->
          (fun _ -> R.error_msg "Static dictionary: Wrong index")
        | Some dict ->
          assert_r (size = Array.length dict)
            "Static dictionary: Wrong size" >|= fun () ->
          catch_r (fun index -> dict.(index))
            ~msg:"Static dictionary: Wrong index"
      
      type dynamic = {
        get : int -> (string, R.msg) result;
        push : string -> unit;
      }
      
      let make_dynamic () =
        let wrong_index_msg = "Dynamic dictionary: Wrong index" in
        let offset = ref 0 in
        let dict = Array.make 128 "" in
        let get = catch_r (fun index -> dict.(index))
          ~msg:wrong_index_msg
        in
        let push str =
          let length = String.length str in
          if length = 0 || length > 128 then () else (
            dict.(!offset) <- str;
            offset := (!offset + 1) mod 128
          )
        in
        { get; push }
        
    end
    
    type context = {
      take : int -> (string, R.msg) result;
      static_dictionary : int -> (string, R.msg) result;
      dynamic_dictionary : Dictionary.dynamic;
    }

    let rec parse_array ~ctx ~length =
      let list_results = List.init length (fun _ -> parse_value ~ctx) in
      list_results |> CCResult.flatten_l
      >|= fun list -> `A list
                
    and parse_object ~ctx ~length =
      let field_results =
        List.init length (fun _ ->
          parse_value ~ctx >>= function
          | `String str ->
            ctx.dynamic_dictionary.push str;
            parse_value ~ctx >|= fun json -> (str, json)
          | _ -> R.error_msg "Object key was not a string"
        )
      in
      field_results |> CCResult.flatten_l
      >|= fun fields -> `O fields

    and parse_string ~ctx ~cache ~length =
      ctx.take length >|= fun str ->
      if cache then ctx.dynamic_dictionary.push str;
      `String str

    (*goto make a 'data-url' in json string*)
    and parse_binary_data ~ctx ~length = parse_string ~ctx ~cache:false ~length

    and parse_value : ctx:context -> (json, _) result =
      fun ~ctx ->
      ctx.take 1 >|= char_of_string >>= fun first_byte ->
      match first_byte |> Bits.explode_byte with

      (*Dynamic dictionary lookup*)
      | 0::_ ->
        let index = first_byte |> int_of_byte ~drop_bits_left:1 in
        ctx.dynamic_dictionary.get index >|= fun str -> 
        `String str

      (*Int*)
      | 1::0::_ ->
        let int = first_byte |> int_of_byte ~drop_bits_left:2 in
        Ok (`Float (float (int-16)))

      (*Static dictionary lookup*)
      | 1::1::0::0::0::_ ->
        ctx.take 1 >>= fun second_byte ->
        let index =
          (CCString.of_char first_byte ^ second_byte)
          |> int_of_byte_string ~drop_bits_left:5
        in
        ctx.static_dictionary index >|= fun str -> 
        `String str

      (*Int*)
      | 1::1::0::0::1::_ ->
        ctx.take 1 >|= fun second_byte ->
        let int =
          (CCString.of_char first_byte ^ second_byte)
          |> int_of_byte_string ~drop_bits_left:5
        in
        `Float (float (int+1008))

      (*Array*)
      | 1::1::0::1::0::_ -> 
        let length = first_byte |> int_of_byte ~drop_bits_left:5 in
        parse_array ~ctx ~length

      (*Object*)
      | 1::1::0::1::1::_ -> 
        let length = first_byte |> int_of_byte ~drop_bits_left:5 in
        parse_object ~ctx ~length

      (*String*)
      | 1::1::1::0::0::_ -> 
        let length = first_byte |> int_of_byte ~drop_bits_left:5 in
        parse_string ~ctx ~cache:true ~length 
        
      (*Binary data*)
      | 1::1::1::0::1::_ -> 
        let length = first_byte |> int_of_byte ~drop_bits_left:5 in
        parse_binary_data ~ctx ~length

      (*Array*)
      | 1::1::1::1::0::0::0::0::_ ->
        ctx.take 2 >|= int_of_byte_string ~drop_bits_left:0 >>= fun length ->
        parse_array ~ctx ~length
          
      (*Object*)
      | 1::1::1::1::0::0::0::1::_ ->
        ctx.take 2 >|= int_of_byte_string ~drop_bits_left:0 >>= fun length ->
        parse_object ~ctx ~length

      (*String*)
      | 1::1::1::1::0::0::1::0::_ ->
        ctx.take 2 >|= int_of_byte_string ~drop_bits_left:0 >>= fun length ->
        parse_string ~ctx ~cache:true ~length

      (*Binary data*)
      | 1::1::1::1::0::0::1::1::_ ->
        ctx.take 2 >|= int_of_byte_string ~drop_bits_left:0 >>= fun length ->
        parse_binary_data ~ctx ~length

      (*Array*)
      | 1::1::1::1::0::1::0::0::_ ->
        ctx.take 6 >|= int64_of_byte_string ~drop_bits_left:0
        >|= CCInt64.to_int >>= fun length -> (*lossy*)
        parse_array ~ctx ~length

      (*Object*)
      | 1::1::1::1::0::1::0::1::_ ->
        ctx.take 6 >|= int64_of_byte_string ~drop_bits_left:0
        >|= CCInt64.to_int >>= fun length -> (*lossy*)
        parse_object ~ctx ~length

      (*String*)
      | 1::1::1::1::0::1::1::0::_ ->
        ctx.take 6 >|= int64_of_byte_string ~drop_bits_left:0
        >|= CCInt64.to_int >>= fun length -> (*lossy*)
        parse_string ~ctx ~cache:true ~length

      (*Binary data*)
      | 1::1::1::1::0::1::1::1::_ ->
        ctx.take 6 >|= int64_of_byte_string ~drop_bits_left:0
        >|= CCInt64.to_int >>= fun length -> (*lossy*)
        parse_binary_data ~ctx ~length
    
      (*32bit signed integer*)
      | 1::1::1::1::1::0::0::0::_ ->
        ctx.take 4 >|= int32_of_byte_string ~drop_bits_left:0 >|= fun int ->
        `Float (Int32.float_of_bits int)

      (*32bit floating point number*)
      | 1::1::1::1::1::0::0::1::_ ->
        ctx.take 4 >|= int32_of_byte_string ~drop_bits_left:0 >|= fun int ->
        `Float (Int32.float_of_bits int)

      (*64bit floating point number*)
      | 1::1::1::1::1::0::1::0::_ ->
        ctx.take 8 >|= int64_of_byte_string ~drop_bits_left:0 >|= fun int ->
        `Float (Int64.float_of_bits int)

      (*Reserved*)
      | 1::1::1::1::1::0::1::1::_ ->
        R.error_msg "Reserved value"

      (*Null*)
      | 1::1::1::1::1::1::0::0::_ -> 
        Ok (`Null)

      (*False*)
      | 1::1::1::1::1::1::0::1::_ ->
        Ok (`Bool false)

      (*True*)
      | 1::1::1::1::1::1::1::0::_ ->
        Ok (`Bool true)

      (*Reserved*)
      | 1::1::1::1::1::1::1::1::_ ->
        R.error_msg "Reserved value"

      (*... *)
      | _ -> R.error_msg "Unknown value"

    let parse_to_json ~static_dictionary ~source =
      let take =
        let stream = source |> ByteStream.of_source in
        fun n -> stream |> ByteStream.take n
      in
      take 4 >>= fun magic_number' ->
      assert_r (magic_number = magic_number') "Magic number" >>= fun () -> 
      take 1 >>= fun version' -> 
      assert_r (version = version') "Version" >>= fun () ->
      take 1 >>= fun _reserved -> 
      take 2 >|= int_of_byte_string ~drop_bits_left:4
      >>= fun static_dictionary_size ->
      assert_r (static_dictionary_size <= 2048) "Static dictionary size" >>= fun () ->
      begin
        Dictionary.make_static ~size:static_dictionary_size static_dictionary
        >|= fun static_dictionary -> 
        let dynamic_dictionary = Dictionary.make_dynamic () in
        {
          take;
          static_dictionary;
          dynamic_dictionary
        }
      end >>= fun ctx -> 
      parse_value ~ctx
      |> CCResult.map_err (fun (`Msg msg) ->
        R.msg @@ "Parse error: "^msg)
    
  end
  
end

(*goto todo;
  * insert performance-test code
    * return median + avg time spent on decoding 
    * howto/spec; 
      * take json + static dictionary as cli-params
      * init: construct a list of stream type clones containing json 
        * type: gen, seq, sequence ..
  * test performance of a more low-level way of matching on bits
    * (extra); cool lib; ppx-extension for pmatching on bits like a list 
    * spec; 
      * shift-right to match bit-block size
      * pmatch on 0bxxx..?
*)
let run () =
  let open CCOpt.Infix in
  let source = `Channel Stdlib.stdin in
  let static_dictionary =
    CCOpt.wrap (fun () -> Sys.argv.(1)) ()
    >|= String.split_on_char ','
    >|= Array.of_list
  in
  let open CCResult.Infix in
  Jsonr.Bin.parse_to_json ~static_dictionary ~source
  >|= Ezjsonm.value_to_channel Stdlib.stdout

let () = match run () with
  | Ok () -> ()
  | Error msg -> msg |> R.pp_msg Format.std_formatter 


