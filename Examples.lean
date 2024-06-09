import Mathlib.Data.List.Defs

def a : Fin 7 := 6
def b : Fin 7 := 3
def c : Fin 7 := 2

open List

#eval permutation

def fano_ell (a b c : Fin 7) : Prop :=
  match a with
  | 0 => match b with
         | 1 => match c with
                | 2 => True
                | _ => False
         | 3 => match c with
                | 6 => True
                | _ => False
         | 5 => match c with
                | 4 => True
                | _ => False
         | _ => False
  | 1 => match b with
         | 3 => match c with
                | 5 => True
                | _ => False
         | _ => False
  | 2 => match b with
         | 3 => match c with
                | 4 => True
                | _ => False
         | 6 => match c with
                | 5 => True
                | _ => False
         | _ => False
  | 4 => match b with
         | 6 => match c with
                | 2 => True
                | _ => False
         | _ => False
  | _ => False

#eval fano_ell 5 3 1
