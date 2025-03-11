Require Import ExtrOcamlBasic ExtrOcamlString.
Require Import PIL.PropQuantifiers PIL.DecisionProcedure.
Require PIL.Simp_env.

(* Simplified propositional quantifiers *)
Module Import S := Simp_env.S.
Module Import SPQr := PropQuant S.

Definition isl_E v f := @Ef v Formulas.Modal f.
Definition isl_A v f := @Af v Formulas.Modal f.

(* simp_form seems to improve over simp in most cases.
  Notable exception: (a ∨b) → c *)
Definition isl_simp f := @simp_form Formulas.Modal f.

(* For backward compatibility only *)
Definition isl_simplified_E := isl_E.
Definition isl_simplified_A := isl_A.

Set Extraction Output Directory ".".

Separate Extraction Provable_dec isl_E isl_A isl_simplified_E isl_simplified_A Formulas.weight isl_simp.

