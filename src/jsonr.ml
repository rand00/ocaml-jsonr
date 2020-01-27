
(*As seen in jsonm documentation*)
type json =
  [ `Null
  | `Bool of bool
  | `Float of float
  | `String of string
  | `A of json list
  | `O of (string * json) list ]

module Bits = struct

  type t = int
  
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

  type t = in_channel

  let take : int -> t -> string option = fun n channel ->
    match really_input_string channel n with
    | exception End_of_file -> None
    | s -> Some s

  (* let rec gen ~channel =
   *   take  *)

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
    let int_of_bytestring :
      type int_local.
        (module IntAbstract with type t = int_local)
      -> of_int:(int -> int_local)
      -> drop_bits_left:int
      -> string
      -> int_local
      = fun int_module ~of_int ~drop_bits_left s ->
        let module IntLocal =
          (val int_module : IntAbstract with type t = int_local) in
        let open IntLocal.Infix in
        let byte_length = 8 in
        s
        |> CCString.fold (fun (acc_int, drop_bits_left) byte ->
          if drop_bits_left >= byte_length then
            (acc_int, drop_bits_left - byte_length)
          else
            let drop_bits_now = min byte_length drop_bits_left in
            let filtered_byte = byte |> Bits.drop_left drop_bits_now in
            let acc_int =
              (acc_int lsl byte_length) lor (of_int (Char.code filtered_byte))
            in
            (acc_int, drop_bits_left - drop_bits_now)
        ) (of_int 0, drop_bits_left)
        |> fun (result, _) -> result
    
    let string_of_bytes bs = bs |> Array.map Char.chr |> CCString.of_array

    let char_of_string s =
      assert (String.length s = 1);
      s.[0]

    let int_of_byte_list ~drop_bits_left bytes =
      bytes
      |> CCString.of_list 
      |> int_of_bytestring (module CCInt) ~of_int:CCFun.id ~drop_bits_left

    let magic_number =
      [| 0b11010011; 0b01001010; 0b01010010; 0b01100010 |]
      |> string_of_bytes

    let version =
      [| 0b00000001 |] 
      |> string_of_bytes

    open CCOpt.Infix 

    let rec parse_array ~take ~length =
      let list = List.init length (fun _ -> parse_value ~take |> CCOpt.to_list) in
      if list |> List.exists CCList.is_empty then None else
        Some (`A (list |> List.flatten))

    and parse_object ~take ~length =
      let fields =
        List.init length (fun _ ->
          (*> goto q joakim; is it really right to have any value as field-key?*)
          ( parse_value ~take >>= function
            | `String str -> parse_value ~take >|= fun json -> (str, json)
            | _ -> None )
          |> CCOpt.to_list
        )
      in
      if fields |> List.exists CCList.is_empty then None else
        Some (`O (fields |> List.flatten))

    and parse_string ~take ~length =
      take length >|= fun str ->
      `String str

    (*goto find out if this is the correct json implementation *)
    and parse_binary_data ~take ~length = parse_string ~take ~length

    and parse_value : take:(int -> string option) -> json option =
      fun ~take ->
      take 1 >|= char_of_string >>= fun first_byte ->
      match first_byte |> Bits.explode_byte with

      (*> goto goo*)
      | 0::_ ->
        failwith "todo: lookup dynamic dictionary"
      | 1::0::_ ->
        failwith "todo: integer x-16"
      | 1::1::0::0::0::_ ->
        failwith "todo: static dictionary"
      | 1::1::0::0::1::_ ->
        failwith "todo: 11 bit integer x+1008"

      (*Array*)
      | 1::1::0::1::0::_ -> 
        let length = [ first_byte ] |> int_of_byte_list ~drop_bits_left:5 in
        parse_array ~take ~length

      (*Object*)
      | 1::1::0::1::1::_ -> 
        let length = [ first_byte ] |> int_of_byte_list ~drop_bits_left:5 in
        parse_object ~take ~length

      (*String*)
      | 1::1::1::0::0::_ -> 
        let length = [ first_byte ] |> int_of_byte_list ~drop_bits_left:5 in
        parse_string ~take ~length
        
      (*Binary data*)
      | 1::1::1::0::1::_ -> 
        let length = [ first_byte ] |> int_of_byte_list ~drop_bits_left:5 in
        parse_binary_data ~take ~length

      (*Array*)
      | 1::1::1::1::0::0::0::0::_ ->
        take 2 >|= int_of_bytestring (module CCInt) ~of_int:CCFun.id
          ~drop_bits_left:0 >>= fun length ->
        parse_array ~take ~length
          
      (*Object*)
      | 1::1::1::1::0::0::0::1::_ ->
        take 2 >|= int_of_bytestring (module CCInt) ~of_int:CCFun.id
          ~drop_bits_left:0 >>= fun length ->
        parse_object ~take ~length

      (*String*)
      | 1::1::1::1::0::0::1::0::_ ->
        take 2 >|= int_of_bytestring (module CCInt) ~of_int:CCFun.id
          ~drop_bits_left:0 >>= fun length ->
        parse_string ~take ~length

      (*Binary data*)
      | 1::1::1::1::0::0::1::1::_ ->
        take 2 >|= int_of_bytestring (module CCInt) ~of_int:CCFun.id
          ~drop_bits_left:0 >>= fun length ->
        parse_binary_data ~take ~length

      (*Array*)
      | 1::1::1::1::0::1::0::0::_ ->
        take 6 >|= int_of_bytestring (module CCInt) ~of_int:CCFun.id
          ~drop_bits_left:0 >>= fun length ->
        parse_array ~take ~length

      (*Object*)
      | 1::1::1::1::0::1::0::1::_ ->
        take 6 >|= int_of_bytestring (module CCInt) ~of_int:CCFun.id
          ~drop_bits_left:0 >>= fun length ->
        parse_object ~take ~length

      (*String*)
      | 1::1::1::1::0::1::1::0::_ ->
        take 6 >|= int_of_bytestring (module CCInt) ~of_int:CCFun.id
          ~drop_bits_left:0 >>= fun length ->
        parse_string ~take ~length

      (*Binary data*)
      | 1::1::1::1::0::1::1::1::_ ->
        take 6 >|= int_of_bytestring (module CCInt) ~of_int:CCFun.id
          ~drop_bits_left:0 >>= fun length ->
        parse_binary_data ~take ~length

      (*32bit signed integer*)
      | 1::1::1::1::1::0::0::0::_ ->
        take 4 >|= int_of_bytestring (module CCInt32) ~of_int:CCInt32.of_int
          ~drop_bits_left:0 >|= fun int ->
        `Float (Int32.float_of_bits int)

      (*32bit floating point number*)
      | 1::1::1::1::1::0::0::1::_ ->
        take 4 >|= int_of_bytestring (module CCInt32) ~of_int:CCInt32.of_int
          ~drop_bits_left:0 >|= fun int ->
        `Float (Int32.float_of_bits int)

      (*64bit floating point number*)
      | 1::1::1::1::1::0::1::0::_ ->
        take 8 >|= int_of_bytestring (module CCInt64) ~of_int:CCInt64.of_int
          ~drop_bits_left:0 >|= fun int ->
        `Float (Int64.float_of_bits int)

      (*Reserved*)
      | 1::1::1::1::1::0::1::1::_ ->
        None

      (*Null*)
      | 1::1::1::1::1::1::0::0::_ -> 
        Some (`Null)

      (*False*)
      | 1::1::1::1::1::1::0::1::_ ->
        Some (`Bool false)

      (*True*)
      | 1::1::1::1::1::1::1::0::_ ->
        Some (`Bool true)

      (*Reserved*)
      | 1::1::1::1::1::1::1::1::_ ->
        None

      (*... *)
      | _ -> None

    let parse_to_json ~channel =
      let take n = ByteStream.take n channel in
      take (String.length magic_number) >>= fun magic_number' ->
      assert (magic_number = magic_number');
      take 1 >>= fun version' ->
      assert (version = version');
      take 1 >>= fun _reserved -> 
      take 2 >|= int_of_bytestring (module CCInt) ~of_int:CCFun.id
          ~drop_bits_left:4 >>= fun static_dictionary_size ->
      assert (static_dictionary_size <= 2048);
      parse_value ~take
    
  end
  
end

(*goto todo;
  * insert performance-test code
    * return median + avg time spent on decoding 
    * howto/spec; 
      * take json + static dictionary as cli-params
      * init: construct a list of stream type clones containing json 
        * type: gen, seq, sequence ..
*)
let run () =
  let open CCOpt.Infix in
  let channel = Stdlib.stdin in
  Jsonr.Bin.parse_to_json ~channel
  >|= Ezjsonm.value_to_channel Stdlib.stdout

let () = match run () with
  | Some () -> ()
  | None ->
    print_endline "Some error happened"


