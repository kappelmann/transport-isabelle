(*  Title:      Transport/transport_parse_util.ML
    Author:     Kevin Kappelmann

Parse Utilities used by Transport.
*)
signature TRANSPORT_PARSE_UTIL =
sig

  val check_scan : ('a -> message) -> ('a -> bool) -> 'a -> 'a

  val eq_parser : Token.T list -> string * Token.T list

  val entry_parser : ('a -> 'b * 'c) -> ('c -> 'd * 'e) -> ('e -> 'f * 'g) ->
    'a -> ('b * 'f) * 'g

  val pretty_names : string list -> Pretty.T
  val name_parser : string list -> (string -> 'a) -> Token.T list ->
    'a * Token.T list

  val eq_name_entry : ''a * (''a * 'b) -> bool

  val check_required_entries : ''a list -> (''a * 'b) list -> bool
  val required_entries_parser : (''a * 'b) parser -> (''a -> string) -> ''a list
    -> Token.T list -> (''a * 'b) list * Token.T list

end

structure Transport_Parse_Util : TRANSPORT_PARSE_UTIL =
struct

fun check_scan msg_of p x = if p x then x else Scan.fail_with msg_of x

val eq_parser = Parse.$$$ "\<equiv>" || Parse.$$$ "="

fun entry_parser name_parser delimiter_parser value_parser =
  name_parser --| delimiter_parser -- value_parser

val pretty_names = map Pretty.str #> Pretty.commas #> Pretty.block

fun name_parser names parse_name =
  let
    val pretty_names = pretty_names names |> Pretty.string_of
    val name_parser = Parse.name >> parse_name
  in Parse.group (K pretty_names) name_parser end

fun eq_name_entry (rn, (xn, _)) = rn = xn

fun check_required_entries rs xs = subset eq_name_entry (rs, xs)

fun required_entries_parser entry_parser param_name_to_string rs =
  let
    fun failure_msg xs _ = Pretty.breaks [
        Pretty.block [
          Pretty.str "Missing parameters: ",
          pretty_names (map param_name_to_string
            (subtract (eq_name_entry o swap) xs rs)),
          Pretty.str "."
        ],
        Pretty.block [
          Pretty.str "Required: ",
          pretty_names (map param_name_to_string rs)
        ]
      ]
      |> Pretty.block
      |> Pretty.string_of
  in
    Parse.and_list1 entry_parser >> check_scan failure_msg (check_required_entries rs)
  end

end