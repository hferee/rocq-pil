open Printer
open PIL.Formulas
open Sys
open Char
open PIL.Extraction
open Stringconversion
open Modal_expressions_parser


let nb_args = Array.length Sys.argv

let form = if nb_args = 2 then (Sys.argv.(1)) else "T"

let () = print_endline (string_of_int (int_of_nat (weight Modal (eval form))))
