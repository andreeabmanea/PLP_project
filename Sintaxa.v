Require Import Strings.String.
Local Open Scope string_scope. 
Local Open Scope list_scope.
Scheme Equality for string.
Require Export Bool.
Definition Var:= string.
Check "x".

Inductive Natural :=
| errnat : Natural
| num : nat -> Natural.

Inductive Boolean :=
| errbool : Boolean
| boolean : bool -> Boolean.

Coercion num: nat >-> Natural.
Coercion boolean: bool >-> Boolean.

Inductive Data :=
| undecl : Data
| assign : Data
| default : Data
| nat_type : Natural -> Data
| bool_type : Boolean -> Data.

Scheme Equality for Data.

Definition Env := string -> Data.

Inductive AExp :=
| avar : string -> AExp
| anum : Natural -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp
| amin : AExp -> AExp -> AExp
| amod : AExp -> AExp -> AExp 
| adiv : AExp -> AExp -> AExp.

(*Notatii folosite pentru expresii aritmetice*)
Notation "A +' B" := (aplus A B) (at level 48).
Notation "A -' B" := (amin A B) (at level 48).
Notation "A /' B" := (adiv A B) (at level 46).
Notation "A *' B" := (amul A B) (at level 46).
Notation "A %' B" := (amod A B) (at level 47).

Coercion anum: Natural >-> AExp.
Coercion avar: string >-> AExp.

Check "x".

Inductive BExp :=
| true 
| false
| bequal : AExp -> AExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| bor : BExp -> BExp -> BExp
| bxor : BExp -> BExp -> BExp. (*sintaxa pentru xor*)

(*Notatii folosite pentru expresii booleane*)
Notation "A <=' B" := (blessthan A B) (at level 53).
Notation "! A" := (bnot A) (at level 52).
Notation "A &&' B" := (band A B) (at level 53).
Notation "A ||' B" := (bor A B) (at level 54).
Notation "A \\ B " := (bxor A B) (at level 54).
Notation "A ==' B" := (bequal A B) (at level 53).

Inductive Instructiune :=
| decl_nat : string -> Instructiune
| atribuire_nat : string -> AExp -> Instructiune
| decl_bool : string -> Instructiune
| atribuire_bool : string -> BExp -> Instructiune
| incrementare : string -> AExp -> Instructiune (*sintaxa incrementare*)
| decrementare : string -> AExp -> Instructiune (*sintaxa decrementare*)
| secventa : Instructiune -> Instructiune -> Instructiune
| while : BExp -> Instructiune -> Instructiune
| ifthen : BExp -> Instructiune -> Instructiune
| ifthenelse : BExp -> Instructiune -> Instructiune -> Instructiune
| comment : string -> Instructiune (*sintaxa pentru comentarii*)
| break : Instructiune
| body_functie : string -> Instructiune -> Instructiune. (*pentru functii*)

(*Notatii folosite pentru instructiuni*)

Notation "break()' " := (break) (at level 50).
Notation "S1 ;; S2" := (secventa S1 S2) (at level 90).
Notation "<nat> X" := (decl_nat X) (at level 60).
Notation "<bool> X" := (decl_bool X) (at level 60).
Notation "X =n A" := (atribuire_nat X A) (at level 60).
Notation "X =b A" := (atribuire_bool X A) (at level 60).
Notation "X ++" := (incrementare X 1) (at level 60).
Notation "X --" := (decrementare X 1) (at level 60).
Notation "'fors' ( A , B , C ) { S }" := (A ;; while B ( S ;; C )) (at level 97).
Notation " // A // " := (comment A) (at level 99).
Notation "f( X ) {{ S }} " := (body_functie X S) (at level 90).
Notation " A ? B ~ C" := (ifthenelse A B C) (at level 65). (*sintaxa operator "?"*)
Notation "'switch'  'case' ( A ) ( B ) ( 'case' ( C )  ( D ) 'default' ( E ))" := (ifthenelse A B (ifthenelse C D E)) (at level 66).
(*sintaxa switch*)
(* switch(x) 
  case 1: x++
  case 2: x--
  default: x=0 
ar putea fi scrisa cu ajutorul a doua ifthenelse-uri: 
if (x==1) then x++ 
  else if (x==2) then x--
        else x=0*)


(*Verificari*)
Check <nat> "a".
Check "x" =n 12.
Check "b" =b true.
Check "x"++.

Definition for_check :=
<nat> "i" ;;
fors ( "i" =n 1 , "i" <=' 10 , "i" =n "i" +' 1 ) {<nat> "x"}.
Check for_check.

Definition op_conditional_check :=
<nat> "x" ;;
("x"=='3) ? ("x"++) ~ ("x"--).
Check op_conditional_check.

Definition switch_check := 
switch 
 case ("x" ==' 1)  ( "x"++ ) 
( case ("x" =='2)  ( "x"-- ) 
     default ( "x" =n 0 )). 
Check switch_check.

Definition functie_check :=
f("nume_functie") {{ <nat> "x" ;; "x" =n 3 }}.
Check functie_check.

Definition while_check :=
while ("i" <=' 6) 
        ("sum" =n "sum" +' "i" ;;
           "i" =n "i" +' 1).
Check while_check.

Definition limbaj1 :=
<nat> "a" ;;
<nat> "b" ;;
<nat> "c" ;; // "exemplu de comentariu" // ;;
"c" =n "a" +' "b" ;;
"c" ++ ;;
break()' ;;
<nat> "i" ;;
<nat> "p" ;;
ifthenelse ("p" <=' "i") ("p" =n 5)
         ("p" =n 4).

Compute limbaj1.

(*Erori*)

Definition div_zero (n1 n2 : Natural) : Natural :=
match n1, n2 with 
| errnat, _ => errnat
| _, errnat => errnat
| _, num 0 => errnat
| num m1, num m2 => num (Nat.div m1 m2)
end.

Definition subst_fst_gt_scnd (n1 n2 : Natural) : Natural :=
match n1, n2 with
| errnat, _ => errnat
| _, errnat => errnat
| num m1, num m2 => if Nat.ltb m1 m2
                    then errnat
                    else num (m1 - m2)
end.
