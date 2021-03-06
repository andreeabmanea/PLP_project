(*Sintaxa*)

Require Import Strings.String.
Local Open Scope string_scope.
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
| nat_type : nat -> Data
| bool_type : bool -> Data.

Scheme Equality for Data.

Definition Env := string -> Data.

Definition check_data_Types (t1 : Data) (t2 : Data) : bool :=
match t1 with
|undecl => match t2 with | undecl => true
                         | _ => false
            end
|assign => match t2 with | assign => true
                         | _ => false
           end
|default => match t2 with | default => true
                          | _ => false
           end
|nat_type n => match t2 with | nat_type m => true
                             | _ => false
           end
|bool_type b1 => match t2 with | bool_type b2 => true
                               | _ => false
           end
end.

Definition update ( env : Env ) ( x : string ) ( v : Data) : Env :=
  fun y =>
   if( string_eq_dec y x)
       then 
          if (andb (check_data_Types undecl (env y)) (negb (check_data_Types default v)))
          then undecl 
          else
             if( andb (check_data_Types undecl (env y))  (check_data_Types default v))
             then default
             else
                 if (orb (check_data_Types default (env y)) (check_data_Types v (env y)))
                 then v 
                 else assign
   else (env y).

Notation "S [ V /' X ]" := (update S X V) (at level 0).

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
| btrue
| bfalse
| berror
| bvar : string -> BExp
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
| break : Instructiune (*sintaxa pentru break*)
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
(*sintaxa instructiune switch*)
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
Check "b" =b btrue.
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

(*Semantica*)

(*Notatii pentru semantica Big-Step*)
Reserved Notation "A =[ S ]=> N" (at level 60).
Reserved Notation "B ={ S }=> B'" (at level 70).

Definition plusNat (n1 n2 : Natural) : Natural :=
  match n1, n2 with
    | errnat, _ => errnat
    | _, errnat => errnat
    | num v1, num v2 => num (v1 + v2)
    end.

Definition subNat (n1 n2 : Natural) : Natural :=
  match n1, n2 with
    | errnat, _ => errnat
    | _, errnat => errnat
    | num n1, num n2 => if Nat.ltb n1 n2
                        then errnat
                        else num (n1 - n2)
    end.

Definition mulNat (n1 n2 : Natural) : Natural :=
  match n1, n2 with
    | errnat, _ => errnat
    | _, errnat => errnat
    | num v1, num v2 => num (v1 * v2)
    end.

Definition divNat (n1 n2 : Natural) : Natural :=
  match n1, n2 with
    | errnat, _ => errnat
    | _, errnat => errnat
    | _, num 0 => errnat
    | num v1, num v2 => num (Nat.div v1 v2)
    end.

Definition modNat (n1 n2 : Natural) : Natural :=
  match n1, n2 with
    | errnat, _ => errnat
    | _, errnat => errnat
    | _, num 0 => errnat
    | num v1, num v2 => num (Nat.modulo v1 v2)
    end.
(*Semantica Big-Step pentru expresii aritmetice*)
Inductive aeval : AExp -> Env -> Natural -> Prop :=
| const : forall n sigma, anum n =[ sigma ]=> n
| var : forall v sigma, avar v =[ sigma ]=>  match (sigma v) with
                                              | nat_type x => x
                                              | _ => errnat
                                              end
| add : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (plusNat i1 i2) ->
    a1 +' a2 =[sigma]=> n
| times : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (mulNat i1 i2) ->
    a1 *' a2 =[sigma]=> n
| substract : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (subNat i1 i2) ->
    a1 -' a2 =[sigma]=> n
| division : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (divNat  i1 i2) ->
    a1 /' a2 =[sigma]=> n
| modulo : forall a1 a2 i1 i2 sigma n,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    n = (modNat i1 i2) ->
    a1 %' a2 =[sigma]=> n
where "a =[ sigma ]=> n" := (aeval a sigma n).

Definition env : Env := fun n => undecl.
Compute (env "x").
Example impartire_la_zero : 10 /' 0 =[ env ]=> errnat.
Proof.
  eapply division.
  - apply const.
  - apply const.
  - simpl. reflexivity.
Qed.

(*Semantica pentru expresii booleane*)
Definition ltBool (n1 n2 : Natural) : Boolean :=
  match n1, n2 with
    | errnat, _ => errbool
    | _, errnat => errbool
    | num v1, num v2 => boolean (Nat.ltb v1 v2)
    end.

Definition notBool (n : Boolean) : Boolean :=
  match n with
    | errbool => errbool
    | boolean v => boolean (negb v)
    end.

Definition andBool (n1 n2 : Boolean) : Boolean :=
  match n1, n2 with
    | errbool, _ => errbool
    | _, errbool => errbool
    | boolean v1, boolean v2 => boolean (andb v1 v2)
    end.

Definition orBool (n1 n2 : Boolean) : Boolean :=
  match n1, n2 with
    | errbool, _ => errbool
    | _, errbool => errbool
    | boolean v1, boolean v2 => boolean (orb v1 v2)
    end.

Definition xorBool (n1 n2 : Boolean) : Boolean :=
   match n1, n2 with
    | errbool, _ => errbool
    | _, errbool => errbool
    | boolean v1, boolean v2 => if (eqb v1 v2)
                              then false 
                              else true
end.
(*tabelul pentru XOR are 1 doar cand v1 si v2 is diferite*)

Definition eqBool (n1 n2 : Boolean) : Boolean :=
  match n1, n2 with 
    | errbool, _ => errbool
    | _, errbool => errbool
    | boolean v1, boolean v2 => if (eqb v1 v2)
                                then true 
                                else false
  end.

(*Semantica Big-Step pentru expresii booleane*)
Inductive beval : BExp -> Env -> Boolean -> Prop :=
| b_error: forall sigma, berror  ={ sigma }=> errbool
| b_true : forall sigma, btrue ={ sigma }=> true
| b_false : forall sigma, bfalse ={ sigma }=> false
| b_var : forall v sigma, bvar v ={ sigma }=>  match (sigma v) with
                                                | bool_type x => x
                                                | _ => errbool
                                                end
| b_lessthan : forall a1 a2 i1 i2 sigma b,
    a1 =[ sigma ]=> i1 ->
    a2 =[ sigma ]=> i2 ->
    b = (ltBool i1 i2) ->
    a1 <=' a2 ={ sigma }=> b
| b_not : forall a1 i1 sigma b,
    a1 ={ sigma }=> i1 ->
    b = (notBool i1) ->
    ! a1 ={ sigma }=> b
| b_and : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (andBool i1 i2) ->
    (a1 &&' a2) ={ sigma }=> b 
| b_or : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (orBool i1 i2) ->
    (a1 ||' a2) ={ sigma }=> b 
| b_xor : forall a1 a2 i1 i2 sigma b,
    a1 ={ sigma }=> i1 ->
    a2 ={ sigma }=> i2 ->
    b = (xorBool i1 i2) ->
    (a1 \\ a2) ={ sigma }=> b
where "B ={ S }=> B'" := (beval B S B').

(*Functia update*)

Reserved Notation "S -{ Sigma }-> Sigma'" (at level 60).
(*Semantica Big-Step pentru instructiuni*)

Inductive eval : Instructiune -> Env -> Env -> Prop :=
(*| e_nat_decl: forall a i x sigma sigma',
   a =[ sigma ]=> i ->
   sigma' = (update sigma x (res_nat i)) ->
   (x :n= a) -{ sigma }-> sigma'
| e_nat_assign: forall a i x sigma sigma',
    a =[ sigma ]=> i ->
    sigma' = (update sigma x (res_nat i)) ->
    (x :n= a) -{ sigma }-> sigma'
| e_bool_decl: forall a i x sigma sigma',
   a ={ sigma }=> i ->
   sigma' = (update sigma x (res_bool i)) ->
   (x :b= a) -{ sigma }-> sigma'
| e_bool_assign: forall a i x sigma sigma',
    a ={ sigma }=> i ->
    sigma' = (update sigma x (res_bool i)) ->
    (x :b= a) -{ sigma }-> sigma'*)
| e_secv : forall s1 s2 sigma sigma1 sigma2,
    s1 -{ sigma }-> sigma1 ->
    s2 -{ sigma1 }-> sigma2 ->
    (s1 ;; s2) -{ sigma }-> sigma2
| e_if_then : forall b s sigma,
    ifthen b s -{ sigma }-> sigma
| e_if_then_elsetrue : forall b s1 s2 sigma sigma',
    b ={ sigma }=> true ->
    s1 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_if_then_elsefalse : forall b s1 s2 sigma sigma',
    b ={ sigma }=> false ->
    s2 -{ sigma }-> sigma' ->
    ifthenelse b s1 s2 -{ sigma }-> sigma' 
| e_whilefalse : forall b s sigma,
    b ={ sigma }=> false ->
    while b s -{ sigma }-> sigma
| e_whiletrue : forall b s sigma sigma',
    b ={ sigma }=> true ->
    (s ;; while b s) -{ sigma }-> sigma' ->
    while b s -{ sigma }-> sigma'
where "s -{ sigma }-> sigma'" := (eval s sigma sigma').



