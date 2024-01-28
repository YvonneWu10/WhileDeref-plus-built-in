Require Import Coq.Lists.List.
Require Import Streams.
Require Import Coq.ZArith.ZArith.
Require Import compcert.lib.Integers.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Strings.String.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Coq.Logic.Classical_Prop.
Require Import compcert.lib.Integers.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import compcert.lib.Integers.
Local Open Scope sets.
Local Open Scope Z.
Local Open Scope bool.

(* event即为输入或输出，均为int64 *)
Inductive event: Type := 
| inevent (i: int64): event
| outevent (i: int64): event.

(* event_list表示有穷多个输入输出，event_stream表示无穷多个输入输出 *)
Notation "'event_list'" := (list event).
Notation "'event_stream'" := (Stream event).

Inductive val: Type :=
| Vuninit: val
| Vint (i: int64): val.

Definition var_name: Type := string.

Record State: Type := {
  vars: var_name -> val;
  mem: int64 -> option val;
}.

Notation "s '.(vars)'" := (vars s) (at level 1).
Notation "s '.(mem)'" := (mem s) (at level 1).

Notation "x :: y" := (cons x y)
(at level 60, right associativity).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

Module EDenote.

(* 表达式的语义为，在state下，给予event_list输入输出操作，可以得到类型为int64的值，或error *)
Record EDenote: Type := {
  nrm: State -> event_list -> int64 -> Prop;
  err: State -> event_list -> Prop;
}.

End EDenote.

Import EDenote.

Notation "x '.(nrm)'" := (EDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (EDenote.err x)
  (at level 1, only printing).

Ltac any_nrm x := exact (EDenote.nrm x).

Ltac any_err x := exact (EDenote.err x).

Notation "x '.(nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).

Notation "x '.(err)'" := (ltac:(any_err x))
  (at level 1, only parsing).


(** readint表达式的值，即为输入的int64 *)
Definition readint_sem_nrm
             (s: State)
             (el: event_list)
             (i: int64): Prop :=
    el = [inevent i].

(** read_int不存在error的情况 *)
Definition readint_sem: EDenote :=
  {|
    nrm := readint_sem_nrm;
    err := ∅;
  |}.

Inductive binop : Type :=
  | OOr | OAnd
  | OLt | OLe | OGt | OGe | OEq | ONe
  | OPlus | OMinus | OMul | ODiv | OMod.

Inductive unop : Type :=
  | ONot | ONeg.

Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EBinop (op: binop) (e1 e2: expr): expr
  | EUnop (op: unop) (e: expr): expr
  | EDeref (e: expr): expr
  | ERead: expr .

Inductive com : Type :=
  | CSkip: com
  | CWrite (e: expr): com
  | CAsgnVar (x: var_name) (e: expr): com
  | CAsgnDeref (e1 e2: expr): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com.

Definition arith_compute1_nrm
             (Zfun: Z -> Z -> Z)
             (i1 i2 i: int64): Prop :=
  let res := Zfun (Int64.signed i1) (Int64.signed i2) in
    i = Int64.repr res /\
    Int64.min_signed <= res <= Int64.max_signed.

Definition arith_compute1_err
             (Zfun: Z -> Z -> Z)
             (i1 i2: int64): Prop :=
  let res := Zfun (Int64.signed i1) (Int64.signed i2) in
    res < Int64.min_signed \/ res > Int64.max_signed.

(* expr1 op expr2，则整个表达式的event_list定义为两个子表达式的event_list的拼接 *)
Definition arith_sem1_nrm
             (Zfun: Z -> Z -> Z)
             (D1 D2: State -> event_list -> int64 -> Prop)
             (s: State)
             (el: event_list)
             (i: int64): Prop :=
  exists i1 i2 el1 el2,
    D1 s el1 i1 /\ D2 s el2 i2 /\
    arith_compute1_nrm Zfun i1 i2 i /\
    el = el1 ++ el2.

(* D1出错，或D1正常运行，D2出错，或D1 op D2出错 *)
Definition arith_sem1_err
             (Zfun: Z -> Z -> Z)
             (D1_nrm D2_nrm: State -> event_list -> int64 -> Prop)
             (D1_err D2_err: State -> event_list -> Prop)
             (s: State)
             (el: event_list): Prop :=
  D1_err s el \/
  (exists i1 el1 el2,
    el = el1 ++ el2 /\
    D1_nrm s el1 i1 /\ D2_err s el2) \/
  (exists i1 i2 el1 el2,
    D1_nrm s el1 i1 /\ D2_nrm s el2 i2 /\
    arith_compute1_err Zfun i1 i2 /\
    el = el1 ++ el2).

Definition arith_sem1 Zfun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem1_nrm Zfun D1.(nrm) D2.(nrm);
    err := arith_sem1_err Zfun D1.(nrm) D2.(nrm) D1.(err) D2.(err);
  |}.

Definition arith_compute2_nrm
             (int64fun: int64 -> int64 -> int64)
             (i1 i2 i: int64): Prop :=
  i = int64fun i1 i2 /\
  Int64.signed i2 <> 0 /\
  (Int64.signed i1 <> Int64.min_signed \/
   Int64.signed i2 <> - 1).

Definition arith_compute2_err (i1 i2: int64): Prop :=
  Int64.signed i2 = 0 \/
  (Int64.signed i1 = Int64.min_signed /\
   Int64.signed i2 = - 1).

(* expr1 op expr2，则整个表达式的event_list定义为两个子表达式的event_list的拼接 *)
Definition arith_sem2_nrm
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: State -> event_list -> int64 -> Prop)
             (s: State)
             (el: event_list)
             (i: int64): Prop :=
  exists i1 i2 el1 el2,
    D1 s el1 i1 /\ D2 s el2 i2 /\
    arith_compute2_nrm int64fun i1 i2 i /\
    el = el1 ++ el2.

(* D1出错，或D1正常运行，D2出错，或D1 op D2出错 *)
Definition arith_sem2_err
             (D1_nrm D2_nrm: State -> event_list -> int64 -> Prop)
             (D1_err D2_err: State -> event_list -> Prop)
             (s: State)
             (el: event_list): Prop :=
  D1_err s el \/
  (exists i1 el1 el2,
    el = el1 ++ el2 /\
    D1_nrm s el1 i1 /\ D2_err s el2) \/
  (exists i1 i2 el1 el2,
    D1_nrm s el1 i1 /\ D2_nrm s el2 i2 /\
    arith_compute2_err i1 i2 /\
    el = el1 ++ el2).

Definition arith_sem2 int64fun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem2_nrm int64fun D1.(nrm) D2.(nrm);
    err := arith_sem2_err D1.(nrm) D2.(nrm) D1.(err) D2.(err);
  |}.

Definition cmp_compute_nrm
             (c: comparison)
             (i1 i2 i: int64): Prop :=
  i = if Int64.cmp c i1 i2
      then Int64.repr 1
      else Int64.repr 0.

(* expr1 op expr2，则整个表达式的event_list定义为两个子表达式的event_list的拼接 *)
Definition cmp_sem_nrm
             (c: comparison)
             (D1 D2: State -> event_list -> int64 -> Prop)
             (s: State)
             (el: event_list)
             (i: int64): Prop :=
  exists i1 i2 el1 el2,
    D1 s el1 i1 /\ D2 s el2 i2 /\
    cmp_compute_nrm c i1 i2 i /\
    el = el1 ++ el2.

(* D1出错，或D1正常运行，D2出错 *)
Definition cmp_sem_err
             (D1_nrm: State -> event_list -> int64 -> Prop)
             (D1_err D2_err: State -> event_list -> Prop)
             (s: State)
             (el: event_list): Prop :=
  D1_err s el \/
  (exists i1 el1 el2,
    el = el1 ++ el2 /\
    D1_nrm s el1 i1 /\ D2_err s el2).

Definition cmp_sem c (D1 D2: EDenote): EDenote :=
  {|
    nrm := cmp_sem_nrm c D1.(nrm) D2.(nrm);
    err := cmp_sem_err D1.(nrm) D1.(err) D2.(err);
  |}.

(* 一元运算语义定义与原本相似 *)
Definition neg_compute_nrm (i1 i: int64): Prop :=
  i = Int64.neg i1 /\
  Int64.signed i1 <> Int64.min_signed.

Definition neg_compute_err (i1: int64): Prop :=
  Int64.signed i1 = Int64.min_signed.

Definition neg_sem_nrm
             (D1: State -> event_list -> int64 -> Prop)
             (s: State)
             (el: event_list)
             (i: int64): Prop :=
  exists i1, 
    D1 s el i1 /\ neg_compute_nrm i1 i.

Definition neg_sem_err
             (D1: State -> event_list -> int64 -> Prop)
             (s: State)
             (el: event_list): Prop :=
  exists i1, D1 s el i1 /\ neg_compute_err i1.

Definition neg_sem (D1: EDenote): EDenote :=
  {|
    nrm := neg_sem_nrm D1.(nrm);
    err := D1.(err) ∪ neg_sem_err D1.(nrm);
  |}.

Definition not_compute_nrm (i1 i: int64): Prop :=
  Int64.signed i1 <> 0 /\ i = Int64.repr 0 \/
  i1 = Int64.repr 0 /\ i = Int64.repr 1.

Definition not_sem_nrm
             (D1: State -> event_list -> int64 -> Prop)
             (s: State)
             (el: event_list)
             (i: int64): Prop :=
  exists i1, D1 s el i1 /\ not_compute_nrm i1 i.

Definition not_sem (D1: EDenote): EDenote :=
  {|
    nrm := not_sem_nrm D1.(nrm);
    err := D1.(err);
  |}.

Definition SC_and_compute_nrm (i1 i: int64): Prop :=
  i1 = Int64.repr 0 /\ i = Int64.repr 0.

Definition SC_or_compute_nrm (i1 i: int64): Prop :=
  Int64.signed i1 <> 0 /\ i = Int64.repr 1.

Definition NonSC_and (i1: int64): Prop :=
  Int64.signed i1 <> 0.

Definition NonSC_or (i1: int64): Prop :=
  i1 = Int64.repr 0.

Definition NonSC_compute_nrm (i2 i: int64): Prop :=
  i2 = Int64.repr 0 /\ i = Int64.repr 0 \/
  Int64.signed i2 <> 0 /\ i = Int64.repr 1.

(* expr1 op expr2，则整个表达式的event_list定义为两个子表达式的event_list的拼接 *)
Definition and_sem_nrm
             (D1 D2: State -> event_list -> int64 -> Prop)
             (s: State)
             (el: event_list)
             (i: int64): Prop :=
  exists i1 el1 el2,
    el = el1 ++ el2 /\
    D1 s el1 i1 /\
    (SC_and_compute_nrm i1 i \/
     NonSC_and i1 /\
     exists i2,
       D2 s el2 i2 /\ NonSC_compute_nrm i2 i).

(* D1出错；或D1正常运行且非短路求值，D2出错 *)
Definition and_sem_err
             (D1_nrm: State -> event_list -> int64 -> Prop)
             (D1_err D2_err: State -> event_list -> Prop)
             (s: State)
             (el: event_list): Prop :=
  D1_err s el \/
  (exists i1 el1 el2,
    D1_nrm s el1 i1 /\ NonSC_and i1 /\ D2_err s el2 /\ el = el1 ++ el2).

Definition and_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := and_sem_nrm D1.(nrm) D2.(nrm);
    err := and_sem_err D1.(nrm) D1.(err) D2.(err);
  |}.

(* expr1 op expr2，则整个表达式的event_list定义为两个子表达式的event_list的拼接 *)
Definition or_sem_nrm
             (D1 D2: State -> event_list -> int64 -> Prop)
             (s: State)
             (el: event_list)
             (i: int64): Prop :=
  exists i1 el1 el2,
    el = el1 ++ el2 /\
    D1 s el1 i1 /\
    (SC_or_compute_nrm i1 i \/
     NonSC_or i1 /\
     exists i2,
       D2 s el2 i2 /\ NonSC_compute_nrm i2 i).

(* D1出错；或D1正常运行且非短路求值，D2出错 *)
Definition or_sem_err
             (D1_nrm: State -> event_list -> int64 -> Prop)
             (D1_err D2_err: State -> event_list -> Prop)
             (s: State)
             (el: event_list): Prop :=
  D1_err s el \/
  (exists i1 el1 el2,
    D1_nrm s el1 i1 /\ NonSC_or i1 /\ D2_err s el2 /\ el = el1 ++ el2).

Definition or_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := or_sem_nrm D1.(nrm) D2.(nrm);
    err := or_sem_err D1.(nrm) D1.(err) D2.(err);
  |}.

Definition unop_sem (op: unop) (D: EDenote): EDenote :=
  match op with
  | ONeg => neg_sem D
  | ONot => not_sem D
  end.

Definition binop_sem (op: binop) (D1 D2: EDenote): EDenote :=
  match op with
  | OOr => or_sem D1 D2
  | OAnd => and_sem D1 D2
  | OLt => cmp_sem Clt D1 D2
  | OLe => cmp_sem Cle D1 D2
  | OGt => cmp_sem Cgt D1 D2
  | OGe => cmp_sem Cge D1 D2
  | OEq => cmp_sem Ceq D1 D2
  | ONe => cmp_sem Cne D1 D2
  | OPlus => arith_sem1 Z.add D1 D2
  | OMinus => arith_sem1 Z.sub D1 D2
  | OMul => arith_sem1 Z.mul D1 D2
  | ODiv => arith_sem2 Int64.divs D1 D2
  | OMod => arith_sem2 Int64.mods D1 D2
  end.

(* 在常数表达式中，event_list长度必须为0，否则出错，其余条件与原本相同 *)
Definition const_sem (n: Z): EDenote :=
  {|
    nrm := fun s el i =>
             i = Int64.repr n /\
             Int64.min_signed <= n <= Int64.max_signed /\
             Z_of_nat (List.length el) = 0;
    err := fun s el =>
             n < Int64.min_signed \/
             n > Int64.max_signed \/
             Z_of_nat (List.length el) <> 0;
  |}.

(* 在变量表达式中，event_list长度必须为0，否则出错，其余条件与原本相同 *)
Definition var_sem (X: var_name): EDenote :=
  {|
    nrm := fun s el i => 
              s.(vars) X = Vint i /\
              Z_of_nat (List.length el) = 0;
    err := fun s el => 
              s.(vars) X = Vuninit \/
              Z_of_nat (List.length el) <> 0;
  |}.

(* 对解引用的定义与原本相似 *)
Definition deref_sem_nrm
             (D1: State -> event_list -> int64 -> Prop)
             (s: State)
             (el: event_list)
             (i: int64): Prop :=
  exists i1, 
    D1 s el i1 /\ s.(mem) i1 = Some (Vint i).

Definition deref_sem_err
             (D1: State -> event_list -> int64 -> Prop)
             (s: State)
             (el: event_list): Prop :=
  exists i1,
    D1 s el i1 /\
    (s.(mem) i1 = None \/ s.(mem) i1 = Some Vuninit).

Definition deref_sem (D1: EDenote): EDenote :=
  {|
    nrm := deref_sem_nrm D1.(nrm);
    err := D1.(err) ∪ deref_sem_err D1.(nrm);
  |}.


Fixpoint eval_expr (e: expr): EDenote :=
  match e with
  | EConst n =>
      const_sem n
  | EVar X =>
      var_sem X
  | EBinop op e1 e2 =>
      binop_sem op (eval_expr e1) (eval_expr e2)
  | EUnop op e1 =>
      unop_sem op (eval_expr e1)
  | EDeref e1 =>
      deref_sem (eval_expr e1)
  | ERead =>
      readint_sem
  end.


(** 在表达式语义定义的基础上，_[test_true]_与_[test_false]_的定义。*)
Definition test_true
             (D: EDenote):
             State -> event_list -> State -> Prop :=
  fun s1 el s2 =>
    Rels.test (fun s => exists i, D.(nrm) s el i /\
    Int64.signed i <> 0) s1 s2.

Definition test_false
             (D: EDenote):
             State -> event_list -> State -> Prop :=
  fun s1 el s2 =>
    Rels.test (fun s => D.(nrm) s el (Int64.repr 0)) s1 s2.


Module CDenote.

(* 程序语句的语义定义为，从state1，运行command，其中包含event_list的输入输出操作，到达state2，或error，或infinity *)
(* 此处infinity分为两类，仅包含有穷多个输入输出操作，或包含无穷多个输入输出操作 *)
Record CDenote: Type := {
  nrm: State -> event_list -> State -> Prop;
  err: State -> event_list -> Prop;
  cinf: State -> event_list -> Prop;
  ioinf: State -> event_stream -> Prop;
}.

End CDenote.

Import CDenote.

Notation "x '.(nrm)'" := (CDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenote.err x)
  (at level 1, only printing).
  
Notation "x '.(cinf)'" := (CDenote.cinf x)
  (at level 1, only printing).

Notation "x '.(ioinf)'" := (CDenote.ioinf x)
  (at level 1, only printing).

Ltac any_nrm x ::=
  match type of x with
  | EDenote => exact (EDenote.nrm x)
  | CDenote => exact (CDenote.nrm x)
  end.

Ltac any_err x ::=
  match type of x with
  | EDenote => exact (EDenote.err x)
  | CDenote => exact (CDenote.err x)
  end.

Definition skip_sem: CDenote :=
  {|
    nrm := Rels.id;
    err := ∅;
    cinf := ∅;
    ioinf := ∅;
  |}.

(* wrtie(D)，则表达式的event_list，定义为表达式D中包含的输入输出操作，与表达式D的值的输出操作的拼接 *)
Definition writeint_sem_nrm
                  (D: State -> event_list -> int64 -> Prop)
                  (s1: State)
                  (el: event_list)
                  (s2: State) : Prop :=
  exists i el1, 
    D s1 el1 i /\ 
    el = el1 ++ [outevent i] /\
    s1 = s2.

(* 若表达式D不出错，则write操作可以正常运行 *)
Definition writeint_sem (D: EDenote): CDenote :=
{|
  nrm := writeint_sem_nrm D.(nrm);
  err := D.(err);
  cinf := ∅;
  ioinf := ∅;
|}.

(* 对赋值语句的定义和原本相似 *)
Definition asgn_var_sem
             (X: var_name)
             (D: EDenote): CDenote :=
  {|
    nrm := fun s1 el s2 =>
      exists i,
        D.(nrm) s1 el i /\ s2.(vars) X = Vint i /\
        (forall Y, X <> Y -> s2.(vars) Y = s1.(vars) Y) /\
        (forall p, s1.(mem) p = s2.(mem) p);
    err := D.(err);
    cinf := ∅;
    ioinf := ∅;
  |}.

Definition asgn_deref_sem_nrm
             (D1 D2: State -> event_list -> int64 -> Prop)
             (s1: State)
             (el: event_list)
             (s2: State): Prop :=
  exists i1 i2 el1 el2,
    el = el1 ++ el2 /\
    D1 s1 el1 i1 /\
    D2 s1 el2 i2 /\
    s1.(mem) i1 <> None /\
    s2.(mem) i1 = Some (Vint i2) /\
    (forall X, s1.(vars) X = s2.(vars) X) /\
    (forall p, i1 <> p -> s1.(mem) p = s2.(mem) p).

(* D1出错，或D1值的内存无访问权限，或D2出错 *)
Definition asgn_deref_sem_err
             (D1_nrm: State -> event_list -> int64 -> Prop)
             (D1_err D2_err: State -> event_list -> Prop)
             (s1: State)
             (el: event_list): Prop :=
  D1_err s1 el \/
  (exists i1 el1 el2,
    el = el1 ++ el2 /\
    D1_nrm s1 el1 i1 /\ s1.(mem) i1 <> None /\
    D2_err s1 el2) \/
  (exists i1,
    D1_nrm s1 el i1 /\
    s1.(mem) i1 = None).

Definition asgn_deref_sem
             (D1 D2: EDenote): CDenote :=
  {|
    nrm := asgn_deref_sem_nrm D1.(nrm) D2.(nrm);
    err := asgn_deref_sem_err D1.(nrm) D1.(err) D2.(err);
    cinf := ∅;
    ioinf := ∅;
  |}.

(* seq_sem和if_sem按照原本的类比定义 *)
Definition seq_sem (D1 D2: CDenote): CDenote :=
  {|
    nrm := D1.(nrm) ∘ D2.(nrm);
    err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
    cinf := D1.(cinf) ∪ (D1.(nrm) ∘ D2.(cinf));
    ioinf := D1.(ioinf) ∪ (D1.(nrm) ∘ D2.(ioinf));
  |}.

Definition if_sem
             (D0: EDenote)
             (D1 D2: CDenote): CDenote :=
  {|
    nrm := (test_true D0 ∘ D1.(nrm)) ∪
           (test_false D0 ∘ D2.(nrm));
    err := D0.(err) ∪
           (test_true D0 ∘ D1.(err)) ∪
           (test_false D0 ∘ D2.(err));
    cinf := (test_true D0 ∘ D1.(cinf)) ∪
           (test_false D0 ∘ D2.(cinf));
    ioinf := (test_true D0 ∘ D1.(ioinf)) ∪
           (test_false D0 ∘ D2.(ioinf));
  |}.

Fixpoint boundedLB_nrm
           (D0: EDenote)
           (D1: CDenote)
           (n: nat):
  State -> event_list -> State -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘ D1.(nrm) ∘ boundedLB_nrm D0 D1 n0) ∪
      (test_false D0)
  end.

Fixpoint boundedLB_err
           (D0: EDenote)
           (D1: CDenote)
           (n: nat): State -> event_list -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
     (test_true D0 ∘
        ((D1.(nrm) ∘ boundedLB_err D0 D1 n0) ∪
         D1.(err))) ∪
      D0.(err)
  end.

(*test_noio的filter，要求输入的X0是没有包含io事件的*)
Definition test_noio
            (X0: State -> event_list -> Prop): 
            State -> event_list -> Prop :=
  fun s tr => X0 s tr /\ tr = nil. 

(*这里是假设X没有io然后X是while.cinf的情况，和未引入io事件的时候一致*)
Definition is_cinf_noio
             (D0: EDenote)
             (D1: CDenote)
             (X: State -> event_list -> Prop): Prop :=
  X ⊆ (test_true D0 ∘ ((D1.(nrm) ∘ X) ∪ D1.(cinf))).

(*这里n就代表着经历了几个循环可以达到没有io的情况，具体可以分类讨论为D1直接发生cinf（可以含有io）；后续不再有io事件，noio的cinf；继续递归，后续是finite io的情况。本处相当于内部是一个cinf_noio的KT不动点，外面是finite_io的BW不动点*)
Fixpoint is_cinf_finiteio
          (D0: EDenote)
          (D1: CDenote)
          (n: nat): State -> event_list -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘ D1.(cinf)) ∪ test_noio (Sets.general_union (is_cinf_noio D0 D1)) ∪ (test_true D0 ∘ D1.(nrm)) ∘ is_cinf_finiteio D0 D1 n0
  end.

(*保证有io的filter*)
Definition nonsilent (X0:  State -> event_list -> State -> Prop) :
  State -> event_list -> State -> Prop :=
  fun s tr s' => X0 s tr s' /\ tr <> nil.

(*保证没有io的filter*)
Definition silent (X0:  State -> event_list -> State -> Prop) :
  State -> event_list -> State -> Prop :=
  fun s tr s' => X0 s tr s' /\ tr = nil.

(*n次的时候都还是silent的，Rels.id代表还没有执行循环体的情况*)
Fixpoint bounded_noio
          (D0: EDenote)
          (D1: CDenote)
          (n: nat):
          State -> event_list -> State -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      Rels.id ∪ silent (test_true D0 ∘
        D1.(nrm)) ∘ bounded_noio D0 D1 n0
  end.

(*ioinf的情况第一种是在执行完有限次没有io的事件以后进入进入D1的ioinf，第二种是执行完有限次的没有io的事件后，执行到了一次有io的，并继续向下递归定义。本处的重点是保证在有穷多次没有io的事件后总会出现一次io，本处相当于内部用的是BW不动点定义了bounded_noio，外面是一层ioinf的KT不动点*)
Definition is_ioinf
            (D0: EDenote)
            (D1: CDenote)
            (X: State -> event_stream -> Prop): Prop :=
  X ⊆ (⋃ (bounded_noio D0 D1)) ∘ (test_true D0 ∘ D1.(ioinf)) ∪ ((⋃ (bounded_noio D0 D1)) ∘ nonsilent (test_true D0 ∘ D1.(nrm))) ∘ X.

Definition while_sem
             (D0: EDenote)
             (D1: CDenote): CDenote :=
  {|
    nrm := ⋃ (boundedLB_nrm D0 D1);
    err := ⋃ (boundedLB_err D0 D1);
    cinf := ⋃ (is_cinf_finiteio D0 D1);
    ioinf := Sets.general_union (is_ioinf D0 D1);
  |}.

Fixpoint eval_com (c: com): CDenote :=
  match c with
  | CSkip =>
      skip_sem
  | CWrite e =>
      writeint_sem (eval_expr e)
  | CAsgnVar X e =>
      asgn_var_sem X (eval_expr e)
  | CAsgnDeref e1 e2 =>
      asgn_deref_sem (eval_expr e1) (eval_expr e2)
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_expr e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_expr e) (eval_com c1)
  end.

Declare Custom Entry expr_entry.
Notation "[[ e ]]" := e
  (at level 0, e custom expr_entry at level 99).
Notation "( x )" := x
  (in custom expr_entry, x custom expr_entry at level 99).
Notation "x" := x
  (in custom expr_entry at level 0, x constr at level 0).
Notation "f x" := (f x)
  (in custom expr_entry at level 1, only parsing,
   f custom expr_entry,
   x custom expr_entry at level 0).
Notation "x + y" := (EBinop OPlus x y)
  (in custom expr_entry at level 12, left associativity).
Notation "x - y" := (EBinop OMinus x y)
  (in custom expr_entry at level 12, left associativity).
Notation "x * y" := (EBinop OMul x y)
  (in custom expr_entry at level 11, left associativity).
Notation "x / y" := (EBinop ODiv x y)
  (in custom expr_entry at level 11, left associativity).
Notation "x % y" := (EBinop OMod x y)
  (in custom expr_entry at level 11, left associativity).
Notation "x <= y" := (EBinop OLe x y)
  (in custom expr_entry at level 13, no associativity).
Notation "x < y" := (EBinop OLt x y)
  (in custom expr_entry at level 13, no associativity).
Notation "x >= y" := (EBinop OGe x y)
  (in custom expr_entry at level 13, no associativity).
Notation "x > y" := (EBinop OGt x y)
  (in custom expr_entry at level 13, no associativity).
Notation "x == y" := (EBinop OEq x y)
  (in custom expr_entry at level 13, no associativity).
Notation "x != y" := (EBinop ONe x y)
  (in custom expr_entry at level 13, no associativity).
Notation "x && y" := (EBinop OAnd x y)
  (in custom expr_entry at level 14, left associativity).
Notation "x || y" := (EBinop OOr x y)
  (in custom expr_entry at level 15, left associativity).
Notation "! x" := (EUnop ONot x)
  (in custom expr_entry at level 10).
Notation "- x" := (EUnop ONeg x)
  (in custom expr_entry at level 10).
Notation "c1 ; c2" := (CSeq c1 c2)
  (in custom expr_entry at level 20, right associativity).
Notation "'skip'" := (CSkip)
  (in custom expr_entry at level 10).
Notation "'write_int' e" := (CWrite e)
  (in custom expr_entry at level 10).
Notation "'if' e 'then' '{' c1 '}' 'else' '{' c2 '}'" := (CIf e c1 c2)
  (in custom expr_entry at level 19,
   e custom expr_entry at level 5,
   c1 custom expr_entry at level 99,
   c2 custom expr_entry at level 99,
   format  "'if'  e  'then'  '{'  c1  '}'  'else'  '{'  c2  '}'").
Notation "'while' e 'do' '{' c1 '}'" := (CWhile e c1)
  (in custom expr_entry at level 19,
   e custom expr_entry at level 5,
   c1 custom expr_entry at level 99).

Notation "⟦ e ⟧" := (eval_expr e)
  (at level 0, only printing, e custom expr_entry at level 99).
Notation "⟦ c ⟧" := (eval_com c)
  (at level 0, only printing, c custom expr_entry at level 99).

Ltac any_eval x :=
  match goal with
  | |- EDenote => exact (eval_expr x)
  | |- CDenote => exact (eval_com x)
  | _ => match type of x with
         | expr => exact (eval_expr x)
         | com => exact (eval_com x)
         end
  end.

Notation "⟦ x ⟧" := (ltac:(any_eval x))
  (at level 0, only parsing, x custom expr_entry at level 99).

Notation "x × y" := (@Sets.test1 _ (y -> Prop) _ x)
  (no associativity, at level 61): sets_scope.

(** 表达式语义等价 *)
Record eequiv (e1 e2: expr): Prop := {
  nrm_eequiv:
    ⟦ e1 ⟧.(nrm) == ⟦ e2 ⟧.(nrm);
  err_eequiv:
    ⟦ e1 ⟧.(err) == ⟦ e2 ⟧.(err);
}.

(* 在精化关系中，若D1出错，则D1的event_list必须是D0的event_list的前缀 *)
Definition erefine_nrm
           (D0 D1_nrm: State -> event_list -> int64 -> Prop)
           (D1_err: State -> event_list -> Prop): Prop :=
    forall s el1 i1,
      D0 s el1 i1 ->
      D1_nrm s el1 i1 \/
      exists el2 el,
        D1_err s el2 /\ el1 = el2 ++ el.

(* D1的event_list必须是D0的event_list的前缀 *)
Definition erefine_err
          (D0 D1: State -> event_list -> Prop): Prop :=
    forall s el1, 
      D0 s el1 ->
      exists el2 el, 
        D1 s el2 /\ el1 = el2 ++ el.

(** 表达式精化关系 *)
Record erefine (e1 e2: expr): Prop := {
  nrm_erefine:
    erefine_nrm ⟦ e1 ⟧.(nrm) ⟦ e2 ⟧.(nrm) ⟦ e2 ⟧.(err);
  err_erefine:
    erefine_err ⟦ e1 ⟧.(err) ⟦ e2 ⟧.(err);
}.

(** 程序语句语义等价 *)
Record cequiv (c1 c2: com): Prop := {
  nrm_cequiv: ⟦ c1 ⟧.(nrm) == ⟦ c2 ⟧.(nrm);
  err_cequiv: ⟦ c1 ⟧.(err) == ⟦ c2 ⟧.(err);
  cinf_cequiv: ⟦ c1 ⟧.(cinf) == ⟦ c2 ⟧.(cinf);
  ioinf_cequiv: ⟦ c1 ⟧.(ioinf) == ⟦ c2 ⟧.(ioinf);
}.

(* 在精化关系中，若D1出错，则D1的event_list必须是D0的event_list的前缀 *)
Definition crefine_nrm
           (D0 D1_nrm: State -> event_list -> State -> Prop)
           (D1_err: State -> event_list -> Prop): Prop :=
  forall s1 el1 s2,
    D0 s1 el1 s2 ->
    D1_nrm s1 el1 s2 \/
    exists el2 el, 
      D1_err s1 el2 /\ el1 = el2 ++ el.

(* D1的event_list必须是D0的event_list的前缀 *)
Definition crefine_err
           (D0 D1: State -> event_list -> Prop): Prop :=
  forall s el1, 
    D0 s el1 ->
    exists el2 el, 
      D1 s el2 /\ el1 = el2 ++ el.

(* 在精化关系中，若D1出错，则D1的event_list必须是D0的event_list的前缀 *)
Definition crefine_cinf
           (D0 D1_cinf D1_err: State -> event_list -> Prop): Prop :=
  forall s el1,
    D0 s el1 ->
    D1_cinf s el1 \/
    exists el2 el,
      D1_err s el2 /\ el1 = el2 ++ el.

(* 在精化关系中，若D1出错，则D1的event_list必须是D0的event_stream的前缀 *)
Definition crefine_ioinf
           (D0 D1_ioinf: State -> event_stream -> Prop)
           (D1_err: State -> event_list -> Prop): Prop :=
  forall s es1,
    D0 s es1 ->
    D1_ioinf s es1 \/
    exists el2 es,
      D1_err s el2 /\ es1 = (StreamConn.stream_app el2 es).


(** 程序语句精化关系 *)
Record crefine (c1 c2: com): Prop := {
  nrm_crefine:
    crefine_nrm ⟦ c1 ⟧.(nrm) ⟦ c2 ⟧.(nrm) ⟦ c2 ⟧.(err);
  err_crefine:
    crefine_err ⟦ c1 ⟧.(err) ⟦ c2 ⟧.(err);
  cinf_crefine:
    crefine_cinf ⟦ c1 ⟧.(cinf) ⟦ c2 ⟧.(cinf) ⟦ c2 ⟧.(err);
  ioinf_crefine:
    crefine_ioinf ⟦ c1 ⟧.(ioinf) ⟦ c2 ⟧.(ioinf) ⟦ c2 ⟧.(err);
}.

Notation "e1 '~=~' e2" := (eequiv e1 e2)
  (at level 69, only printing, no associativity).
Notation "e1 '<<=' e2" := (erefine e1 e2)
  (at level 69, only printing, no associativity).
Notation "c1 '~=~' c2" := (cequiv c1 c2)
  (at level 69, only printing, no associativity).
Notation "c1 '<<=' c2" := (crefine c1 c2)
  (at level 69, only printing, no associativity).

Ltac any_equiv x y :=
  match type of x with
  | expr => exact (eequiv x y)
  | com => exact (cequiv x y)
  | _ => match type of y with
         | expr => exact (eequiv x y)
         | com => exact (cequiv x y)
         end
  end.

Ltac any_refine x y :=
  match type of x with
  | expr => exact (erefine x y)
  | com => exact (crefine x y)
  | _ => match type of y with
         | expr => exact (erefine x y)
         | com => exact (crefine x y)
         end
  end.


Notation "x '~=~' y" := (ltac:(any_equiv x y))
  (at level 69, only parsing, no associativity).
Notation "x '<<=' y" := (ltac:(any_refine x y))
  (at level 69, only parsing, no associativity).

Notation "H '.(nrm_eequiv)'" := (nrm_eequiv _ _ H)
  (at level 1).
Notation "H '.(err_eequiv)'" := (err_eequiv _ _ H)
  (at level 1).
Notation "H '.(nrm_erefine)'" := (nrm_erefine _ _ H)
  (at level 1).
Notation "H '.(err_erefine)'" := (err_erefine _ _ H)
  (at level 1).
Notation "H '.(nrm_cequiv)'" := (nrm_cequiv _ _ H)
  (at level 1).
Notation "H '.(err_cequiv)'" := (err_cequiv _ _ H)
  (at level 1).
Notation "H '.(cinf_cequiv)'" := (cinf_cequiv _ _ H)
  (at level 1).
Notation "H '.(ioinf_cequiv)'" := (ioinf_cequiv _ _ H)
  (at level 1).
Notation "H '.(nrm_crefine)'" := (nrm_crefine _ _ H)
  (at level 1).
Notation "H '.(err_crefine)'" := (err_crefine _ _ H)
  (at level 1).
Notation "H '.(cinf_crefine)'" := (cinf_crefine _ _ H)
  (at level 1).
Notation "H '.(ioinf_crefine)'" := (ioinf_crefine _ _ H)
  (at level 1).

(* 语义等价是等价关系 *)
Instance eequiv_refl: Reflexive eequiv.
Proof.
  unfold Reflexive; intros.
  split.
  + reflexivity.
  + reflexivity.
Qed.

Instance eequiv_sym: Symmetric eequiv.
Proof.
  unfold Symmetric; intros.
  split.
  + rewrite H.(nrm_eequiv).
    reflexivity.
  + rewrite H.(err_eequiv).
    reflexivity.
Qed.

Instance eequiv_trans: Transitive eequiv.
Proof.
  unfold Transitive; intros.
  split.
  + rewrite H.(nrm_eequiv), H0.(nrm_eequiv).
    reflexivity.
  + rewrite H.(err_eequiv), H0.(err_eequiv).
    reflexivity.
Qed.

Instance eequiv_equiv: Equivalence eequiv.
Proof.
  split.
  + apply eequiv_refl.
  + apply eequiv_sym.
  + apply eequiv_trans.
Qed.

(** 精化关系具有自反性和传递性。*)
Instance erefine_refl: Reflexive erefine.
Proof.
  unfold Reflexive; intros.
  split.
  + unfold erefine_nrm.
    tauto.
  + unfold erefine_err; intros.
    exists el1, nil.
    split; [tauto |].
    rewrite app_nil_r; tauto.
Qed.

Instance erefine_trans: Transitive erefine.
Proof.
  unfold Transitive; intros.
  split; destruct H as [ nrm1 err1 ]; destruct H0 as [ nrm2 err2 ].
  (* nrm的情况 *)
  + unfold erefine_nrm in nrm1, nrm2.
    unfold erefine_nrm; intros.
    specialize (nrm1 s el1 i1).
    pose proof nrm1 H.
    destruct H0.
    - specialize (nrm2 s el1 i1).
      pose proof nrm2 H0; tauto.
    - right.
      destruct H0 as (el2 & el & ?).
      unfold erefine_err in err2.
      specialize (err2 s el2).
      destruct H0.
      pose proof err2 H0.
      destruct H2 as (el3 & el4 & [? ?]).
      exists el3, (el4 ++ el).
      split; [apply H2 |].
      rewrite H1, H3; apply app_assoc_reverse.
  (* err的情况 *)
  + unfold erefine_err; intros.
    unfold erefine_err in err1, err2.
    specialize (err1 s el1).
    pose proof err1 H.
    destruct H0 as (el2 & el & ?); destruct H0.
    specialize (err2 s el2).
    pose proof err2 H0.
    destruct H2 as (el3 & el4 & ?); destruct H2.
    exists el3, (el4 ++ el).
    split; [apply H2 |].
    rewrite H1, H3; apply app_assoc_reverse.
Qed.

Instance cequiv_refl: Reflexive cequiv.
Proof.
  unfold Reflexive; intros.
  split.
  + reflexivity.
  + reflexivity.
  + reflexivity.
  + reflexivity.
Qed.

Instance cequiv_sym: Symmetric cequiv.
Proof.
  unfold Symmetric; intros.
  split.
  + rewrite H.(nrm_cequiv).
    reflexivity.
  + rewrite H.(err_cequiv).
    reflexivity.
  + rewrite H.(cinf_cequiv).
    reflexivity.
  + rewrite H.(ioinf_cequiv).
  reflexivity.
Qed.

Instance cequiv_trans: Transitive cequiv.
Proof.
  unfold Transitive; intros.
  split.
  + rewrite H.(nrm_cequiv), H0.(nrm_cequiv).
    reflexivity.
  + rewrite H.(err_cequiv), H0.(err_cequiv).
    reflexivity.
  + rewrite H.(cinf_cequiv), H0.(cinf_cequiv).
    reflexivity.
  + rewrite H.(ioinf_cequiv), H0.(ioinf_cequiv).
  reflexivity.
Qed.

Instance cequiv_equiv: Equivalence cequiv.
Proof.
  split.
  + apply cequiv_refl.
  + apply cequiv_sym.
  + apply cequiv_trans.
Qed.

(* 程序语句间的精化关系也具有自反性与传递性 *)
(* 自反性 *)
Instance crefine_refl: Reflexive crefine.
Proof.
  unfold Reflexive; intros.
  split.
  (* nrm的情况 *)
  + unfold crefine_nrm; intros.
    tauto.
  (* err的情况 *)
  + unfold crefine_err; intros.
    exists el1, nil.
    split; [apply H |].
    rewrite app_nil_r; tauto.
  (* cinf的情况 *)
  + unfold crefine_cinf; intros.
    left; apply H.
  (* ioinf的情况 *)
  + unfold crefine_ioinf; intros.
    left; apply H.
Qed.

(* 传递性 *)
Instance crefine_trans: Transitive crefine.
Proof.
  unfold Transitive; intros.
  split; destruct H as [ nrm1 err1 cinf1 ioinf1 ]; destruct H0 as [ nrm2 err2 cinf2 ioinf2 ].
  (* nrm的情况 *)
  + unfold crefine_nrm; intros.
    unfold crefine_nrm in nrm1.
    specialize (nrm1 s1 el1 s2).
    pose proof nrm1 H; destruct H0.
    - unfold crefine_nrm in nrm2.
      specialize (nrm2 s1 el1 s2).
      pose proof nrm2 H0; apply H1.
    - right.
      destruct H0 as (el2 & el & ?); destruct H0.
      unfold crefine_err in err2.
      specialize (err2 s1 el2).
      pose proof err2 H0.
      destruct H2 as (el3 & el4 & ?); destruct H2.
      exists el3, (el4 ++ el).
      split; [tauto |].
      rewrite H1, H3; apply app_assoc_reverse.
  (* err的情况 *)
  + unfold crefine_err; intros.
    unfold crefine_err in err1.
    specialize (err1 s el1).
    pose proof err1 H.
    destruct H0 as (el2 & el & ?); destruct H0.
    unfold crefine_err in err2.
    specialize (err2 s el2).
    pose proof err2 H0.
    destruct H2 as (el3 & el4 & ?); destruct H2.
    exists el3, (el4 ++ el).
    split; [tauto |].
    rewrite H1, H3; apply app_assoc_reverse.
  (* cinf的情况 *)
  + unfold crefine_cinf; intros.
    unfold crefine_cinf in cinf1.
    specialize (cinf1 s el1).
    pose proof cinf1 H; destruct H0.
    - unfold crefine_cinf in cinf2.
      specialize (cinf2 s el1).
      pose proof cinf2 H0; apply H1.
    - right.
      destruct H0 as (el2 & el & ?); destruct H0.
      unfold crefine_err in err2.
      specialize (err2 s el2).
      pose proof err2 H0.
      destruct H2 as (el3 & el4 & ?); destruct H2.
      exists el3, (el4 ++ el).
      split; [tauto |].
      rewrite H1, H3; apply app_assoc_reverse.
  (* ioinf的情况 *)
  + unfold crefine_ioinf; intros.
    unfold crefine_ioinf in ioinf1.
    specialize (ioinf1 s es1).
    pose proof ioinf1 H; destruct H0.
    - unfold crefine_ioinf in ioinf2.
      specialize (ioinf2 s es1).
      pose proof ioinf2 H0; apply H1.
    - right.
      destruct H0 as (el2 & es & ?); destruct H0.
      unfold crefine_err in err2.
      specialize (err2 s el2).
      pose proof err2 H0.
      destruct H2 as (el3 & el & ?); destruct H2.
      exists el3, (StreamConn.stream_app el es).
      split; [tauto |].
      rewrite H1, H3.
      apply (StreamConn.stream_ACC_Assoc event).
Qed.

(* arith_sem1能保持精化关系，nrm *)
Lemma arith_sem1_nrm_mono: forall Zfun (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  erefine_nrm (arith_sem1_nrm Zfun ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm))
              (arith_sem1_nrm Zfun ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm))
              (arith_sem1_err Zfun ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm) ⟦ e12 ⟧.(err) ⟦ e22 ⟧.(err)).
Proof.
  intros.
  sets_unfold.
  unfold erefine_nrm.
  intros s el i.
  unfold arith_sem1_nrm, arith_sem1_err. intros.
  destruct H1 as (i1 & i2 & el1 & el2 & ?); destruct H1 as [? [? [? ?] ] ].
  apply H.(nrm_erefine) in H1.
  apply H0.(nrm_erefine) in H2.
  destruct H1.
  (* e12 nrm的情况 *)
  + destruct H2; [left; exists i1, i2, el1, el2; tauto |].
    destruct H2 as (el3 & el4 & ?); destruct H2.
    right; exists (el1 ++ el3), el4.
    split; [| rewrite H4, H5; apply app_assoc].
    right; left; exists i1, el1, el3; tauto.
  (* e12 err的情况 *)
  + destruct H1 as (el3 & el4 & ?); destruct H1.
    destruct H2.
    (* e22 nrm的情况 *)
    - right; exists el3, (el4 ++ el2).
      split; [| rewrite H4, H5; apply app_assoc_reverse]; tauto.
    (* e22 err的情况 *)
    - destruct H2 as (el5 & el6 & ?); destruct H2.
      right; exists el3, (el4 ++ el2).
      split; [| rewrite H4, H6, H5; apply app_assoc_reverse]; tauto.
Qed.

(* arith_sem1能保持精化关系，err *)
Lemma arith_sem1_err_mono: forall Zfun (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  erefine_err (arith_sem1_err Zfun ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ⟦ e11 ⟧.(err) ⟦ e21 ⟧.(err))
              (arith_sem1_err Zfun ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm) ⟦ e12 ⟧.(err) ⟦ e22 ⟧.(err)).
Proof.
  intros.
  unfold erefine_err; intros s el.
  unfold arith_sem1_err; intros.
  destruct H1 as [? | [? | ?] ].
  (* e11 err的情况 *)
  + apply H.(err_erefine) in H1.
    destruct H1 as (el1 & el2 & [? ?]).
    exists el1, el2; tauto.
  (* e21 err的情况*)
  + destruct H1 as (i1 & el1 & el2 & [? [? ?] ]).
    apply H0.(err_erefine) in H3.
    destruct H3 as (el3 & el4 & [? ?]).
    apply H.(nrm_erefine) in H2.
    destruct H2.
    (* e12 nrm的情况 *)
    - exists (el1 ++ el3), el4.
      split; [| rewrite H1, H4; apply app_assoc].
      right; left.
      exists i1, el1, el3; tauto.
    (* e12 err的情况 *)
    - destruct H2 as (el5 & el6 & [? ?]).
      exists el5, (el6 ++ el3 ++ el4).
      split; [tauto | rewrite H1, H5, H4; apply app_assoc_reverse].
  (* arith_compute1_err的情况 *)
  + destruct H1 as (i1 & i2 & el1 & el2 & [? [? [? ?] ] ]).
    apply H.(nrm_erefine) in H1.
    apply H0.(nrm_erefine) in H2.
    destruct H1.
    (* e12 nrm的情况 *)
    - destruct H2.
      (* e22 nrm的情况 *)
      * exists (el1 ++ el2), nil.
        split; [| rewrite H4; rewrite app_nil_r; tauto].
        right; right; exists i1, i2, el1, el2; tauto.
      (* e22 err的情况 *)
      * destruct H2 as (el3 & el4 & [? ?]).
        exists (el1 ++ el3), el4.
        split; [| rewrite H4, H5; apply app_assoc].
        right; left; exists i1, el1, el3; tauto.
    (* e12 err的情况 *)
    - destruct H1 as (el3 & el4 & [? ?]).
      destruct H2.
      (* e22 nrm的情况 *)
      * exists el3, (el4 ++ el2).
        split; [| rewrite H4, H5; apply app_assoc_reverse]; tauto.
      (* e22 err的情况 *)
      * destruct H2 as (el5 & el6 & [? ?]).
        exists el3, (el4 ++ el5 ++ el6).
        split; [| rewrite H4, H6, H5; apply app_assoc_reverse]; tauto.
Qed.

(* arith_sem2能保持精化关系，nrm *)
Lemma arith_sem2_nrm_mono: forall int64fun (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  erefine_nrm (arith_sem2_nrm int64fun ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm))
              (arith_sem2_nrm int64fun ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm))
              (arith_sem2_err ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm) ⟦ e12 ⟧.(err) ⟦ e22 ⟧.(err)).
Proof.
  intros.
  unfold erefine_nrm; intros s el i.
  unfold arith_sem2_nrm, arith_sem2_err; intros.
  destruct H1 as (i1 & i2 & el1 & el2 & [? [? [? ?] ] ]).
  apply H.(nrm_erefine) in H1.
  apply H0.(nrm_erefine) in H2.
  destruct H1.
  (* e12 nrm的情况 *)
  + destruct H2; [left; exists i1, i2, el1, el2; tauto |].
    destruct H2 as (el3 & el4 & [? ?]).
    right; exists (el1 ++ el3), el4.
    split; [| rewrite H4, H5; apply app_assoc].
    right; left; exists i1, el1, el3; tauto.
  (* e12 err的情况 *)
  + destruct H2; destruct H1 as (el3 & el4 & [? ?]).
    (* e22 nrm的情况 *)
    - right; exists el3, (el4 ++ el2).
      split; [| rewrite H4, H5; apply app_assoc_reverse]; tauto.
    (* e22 err的情况 *)
    - destruct H2 as (el5 & el6 & [? ?]).
      right; exists el3, (el4 ++ el5 ++ el6).
      split; [| rewrite H4, H5, H6; apply app_assoc_reverse]; tauto.
Qed.

(* arith_sem2能保持精化关系，err *)
Lemma arith_sem2_err_mono: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  erefine_err (arith_sem2_err ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm) ⟦ e11 ⟧.(err) ⟦ e21 ⟧.(err))
              (arith_sem2_err ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm) ⟦ e12 ⟧.(err) ⟦ e22 ⟧.(err)).
Proof.
  intros.
  unfold erefine_err; intros s el.
  unfold arith_sem2_err; intros.
  destruct H1 as [? | [(i1 & el1 & el2 & [? [? ?] ]) | (i1 & i2 & el1 & el2 & [? [? [? ?] ] ])] ].
  (* e11 err的情况 *)
  + apply H.(err_erefine) in H1.
    destruct H1 as (el1 & el2 & [? ?]).
    exists el1, el2; tauto.
  (* e21 err的情况 *)
  + apply H.(nrm_erefine) in H2.
    apply H0.(err_erefine) in H3.
    destruct H3 as (el3 & el4 & [? ?]).
    destruct H2.
    (* e12 nrm的情况 *)
    - exists (el1 ++ el3), el4.
      split; [| rewrite H1, H4; apply app_assoc].
      right; left; exists i1, el1, el3; tauto.
    (* e12 err的情况 *)
    - destruct H2 as (el5 & el6 & [? ?]).
      exists el5, (el6 ++ el3 ++ el4).
      split; [| rewrite H1, H5, H4; apply app_assoc_reverse]; tauto.
  (* arith_compute2_err的情况 *)
  + apply H.(nrm_erefine) in H1.
    apply H0.(nrm_erefine) in H2.
    destruct H1; destruct H2.
    (* e12 e22都是nrm的情况 *)
    - exists (el1 ++ el2), nil.
      split; [| rewrite H4; rewrite app_nil_r; tauto].
      right; right; exists i1, i2, el1, el2; tauto.
    (* e12 nrm, e22 err的情况 *)
    - destruct H2 as (el3 & el4 & [? ?]).
      exists (el1 ++ el3), el4.
      split; [| rewrite H4, H5; apply app_assoc].
      right; left; exists i1, el1, el3; tauto.
    (* e12 err, e22 nrm的情况 *)
    - destruct H1 as (el3 & el4 & [? ?]).
      exists el3, (el4 ++ el2).
      split; [| rewrite H4, H5; apply app_assoc_reverse]; tauto.
    (* e12 e22都是err的情况 *)
    - destruct H1 as (el3 & el4 & [? ?]).
      destruct H2 as (el5 & el6 & [? ?]).
      exists el3, (el4 ++ el5 ++ el6).
      split; [| rewrite H4, H5, H6; apply app_assoc_reverse]; tauto.
Qed.

(* cmp_sem能保持精化关系，nrm *)
Lemma cmp_sem_nrm_mono: forall op (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  erefine_nrm (cmp_sem_nrm op ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm))
              (cmp_sem_nrm op ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm))
              (cmp_sem_err ⟦ e12 ⟧.(nrm) ⟦ e12 ⟧.(err) ⟦ e22 ⟧.(err)).
Proof.
  intros.
  unfold erefine_nrm; intros s el i.
  unfold cmp_sem_nrm, cmp_sem_err; intros.
  destruct H1 as (i1 & i2 & el1 & el2 & [? [? [? ?] ] ]).
  apply H.(nrm_erefine) in H1.
  apply H0.(nrm_erefine) in H2.
  destruct H1, H2.
  (* e12 e22 都是nrm的情况 *)
  + left; exists i1, i2, el1, el2; tauto.
  (* e12 nrm, e22 err的情况 *)
  + destruct H2 as (el3 & el4 & [? ?]).
    right; exists (el1 ++ el3), el4.
    split; [| rewrite H4, H5; apply app_assoc].
    right; exists i1, el1, el3; tauto.
  (* e12 err, e22 nrm的情况 *)
  + destruct H1 as (el3 & el4 & [? ?]).
    right; exists el3, (el4 ++ el2).
    split; [| rewrite H4, H5; apply app_assoc_reverse]; tauto.
  (* e12 e22 都是err的情况 *)
  + destruct H1 as (el3 & el4 & [? ?]).
    destruct H2 as (el5 & el6 & [? ?]).
    right; exists el3, (el4 ++ el5 ++ el6).
    split; [| rewrite H4, H5, H6; apply app_assoc_reverse]; tauto.
Qed.

(* cmp_sem能保持精化关系，err *)
Lemma cmp_sem_err_mono: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  erefine_err (cmp_sem_err ⟦ e11 ⟧.(nrm) ⟦ e11 ⟧.(err) ⟦ e21 ⟧.(err))
              (cmp_sem_err ⟦ e12 ⟧.(nrm) ⟦ e12 ⟧.(err) ⟦ e22 ⟧.(err)).
Proof.
  intros.
  unfold erefine_err; intros s el.
  unfold cmp_sem_err; intros.
  destruct H1 as [? | (i1 & el1 & el2 & [? [? ?] ])].
  (* e11 err的情况 *)
  + apply H.(err_erefine) in H1.
    destruct H1 as (el1 & el2 & [? ?]).
    exists el1, el2; tauto.
  (* e21 err的情况*)
  + apply H.(nrm_erefine) in H2.
    apply H0.(err_erefine) in H3.
    destruct H3 as (el3 & el4 & [? ?]).
    destruct H2 as [? | (el5 & el6 & [? ?])].
    (* e12 nrm的情况 *)
    - exists (el1 ++ el3), el4.
      split; [| rewrite H1, H4; apply app_assoc].
      right; exists i1, el1, el3; tauto.
    (* e12 err的情况 *)
    - exists el5, (el6 ++ el3 ++ el4).
      split; [| rewrite H1, H5, H4; apply app_assoc_reverse]; tauto.
Qed.

(* and_sem能保持精化关系，nrm *)
Lemma and_sem_nrm_mono: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  erefine_nrm (and_sem_nrm ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm))
              (and_sem_nrm ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm))
              (and_sem_err ⟦ e12 ⟧.(nrm) ⟦ e12 ⟧.(err) ⟦ e22 ⟧.(err)).
Proof.
  intros.
  unfold erefine_nrm; intros s el i.
  unfold and_sem_nrm, and_sem_err; intros.
  destruct H1 as (i1 & el1 & el2 & [? [? [? | [? (i2 & [? ?])] ] ] ]).
  (* 短路求值的情况 *)
  + apply H.(nrm_erefine) in H2.
    destruct H2 as [? | (el3 & el4 & [? ?]) ].
    - left; exists i1, el1, el2; tauto.
    - right; exists el3, (el4 ++ el2).
      split; [| rewrite H1, H4; apply app_assoc_reverse]; tauto.
  (* 非短路求值的情况 *)
  + apply H.(nrm_erefine) in H2.
    apply H0.(nrm_erefine) in H4.
    destruct H2, H4.
    (* e12 e22都是nrm的情况 *)
    - left; exists i1, el1, el2.
      split; [tauto |].
      split; [tauto |].
      right; split; [tauto |].
      exists i2; tauto.
    (* e12 nrm, e22 err的情况 *)
    - destruct H4 as (el3 & el4 & [? ?]).
      right; exists (el1 ++ el3), el4.
      split; [| rewrite H1, H6; apply app_assoc].
      right; exists i1, el1, el3; tauto.
    (* e12 err, e22 nrm的情况 *)
    - destruct H2 as (el3 & el4 & [? ?]).
      right; exists el3, (el4 ++ el2).
      split; [| rewrite H1, H6; apply app_assoc_reverse]; tauto.
    (* e12 e22都是err的情况 *)
    - destruct H2 as (el3 & el4 & [? ?]).
      destruct H4 as (el5 & el6 & [? ?]).
      right; exists el3, (el4 ++ el5 ++ el6).
      split; [| rewrite H1, H6, H7; apply app_assoc_reverse]; tauto.
Qed.

(* and_sem能保持精化关系，err *)
Lemma and_sem_err_mono: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  erefine_err (and_sem_err ⟦ e11 ⟧.(nrm) ⟦ e11 ⟧.(err) ⟦ e21 ⟧.(err))
              (and_sem_err ⟦ e12 ⟧.(nrm) ⟦ e12 ⟧.(err) ⟦ e22 ⟧.(err)).
Proof.
  intros.
  unfold erefine_err; intros s el.
  unfold and_sem_err; intros.
  destruct H1 as [? | (i1 & el1 & el2 & [? [? [? ?] ] ])].
  (* e11 err的情况 *)
  + apply H.(err_erefine) in H1.
    destruct H1 as (el1 & el2 & [? ?]).
    exists el1, el2.
    split; [| tauto]; tauto.
  (* e21 err的情况 *)
  + apply H.(nrm_erefine) in H1.
    apply H0.(err_erefine) in H3.
    destruct H3 as (el5 & el6 & [? ?]).
    destruct H1 as [? |(el3 & el4 & [? ?])].
    (* e12 nrm的情况 *)
    - exists (el1 ++ el5), el6.
      split; [| rewrite H4, H5; apply app_assoc].
      right; exists i1, el1, el5; tauto.
    (* e12 err的情况 *)
    - exists el3, (el4 ++ el5 ++ el6).
      split; [tauto | rewrite H4, H6, H5; apply app_assoc_reverse].
Qed.

(* or_sem能保持精化关系，nrm *)
Lemma or_sem_nrm_mono: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  erefine_nrm (or_sem_nrm ⟦ e11 ⟧.(nrm) ⟦ e21 ⟧.(nrm))
              (or_sem_nrm ⟦ e12 ⟧.(nrm) ⟦ e22 ⟧.(nrm))
              (or_sem_err ⟦ e12 ⟧.(nrm) ⟦ e12 ⟧.(err) ⟦ e22 ⟧.(err)).
Proof.
  intros.
  unfold erefine_nrm; intros s el i.
  unfold or_sem_nrm, or_sem_err; intros.
  destruct H1 as (i1 & el1 & el2 & [? [? [? | [? (i2 & [? ?])] ] ] ]).
  (* 短路求值的情况 *)
  + apply H.(nrm_erefine) in H2.
    destruct H2 as [? | (el3 & el4 & [? ?])].
    (* e12 nrm的情况 *)
    - left; exists i1, el1, el2; tauto.
    (* e12 err的情况 *)
    - right; exists el3, (el4 ++ el2).
      split; [| rewrite H1, H4; apply app_assoc_reverse]; tauto.
  (* 非短路求值的情况 *)
  + apply H.(nrm_erefine) in H2.
    apply H0.(nrm_erefine) in H4.
    destruct H2, H4.
    (* e12 e22都是nrm的情况 *)
    - left; exists i1, el1, el2.
      split; [tauto |].
      split; [tauto |].
      right; split; [tauto |].
      exists i2; tauto.
    (* e12 nrm, e22 err的情况 *)
    - destruct H4 as (el3 & el4 & [? ?]).
      right; exists (el1 ++ el3), el4.
      split; [| rewrite H1, H6; apply app_assoc].
      right; exists i1, el1, el3; tauto.
    (* e12 err, e22 nrm的情况 *)
    - destruct H2 as (el3 & el4 & [? ?]).
      right; exists el3, (el4 ++ el2).
      split; [| rewrite H1, H6; apply app_assoc_reverse]; tauto.
    (* e12 e22都是err的情况 *)
    - destruct H2 as (el3 & el4 & [? ?]).
      destruct H4 as (el5 & el6 & [? ?]).
      right; exists el3, (el4 ++ el5 ++ el6).
      split; [| rewrite H1, H6, H7; apply app_assoc_reverse]; tauto.
Qed.

(* or_sem能保持精化关系，err *)
Lemma or_sem_err_mono: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  erefine_err (or_sem_err ⟦ e11 ⟧.(nrm) ⟦ e11 ⟧.(err) ⟦ e21 ⟧.(err))
              (or_sem_err ⟦ e12 ⟧.(nrm) ⟦ e12 ⟧.(err) ⟦ e22 ⟧.(err)).
Proof.
  intros.
  unfold erefine_err; intros s el.
  unfold or_sem_err; intros.
  destruct H1 as [? | (i1 & el1 & el2 & [? [? [? ?] ] ])].
  (* e11 err的情况 *)
  + apply H.(err_erefine) in H1.
    destruct H1 as (el1 & el2 & [? ?]).
    exists el1, el2; tauto.
  (* e21 err的情况 *)
  + apply H.(nrm_erefine) in H1.
    apply H0.(err_erefine) in H3.
    destruct H3 as (el3 & el4 & [? ?]).
    destruct H1 as [? | (el5 & el6 & [? ?])].
    (* e12 nrm的情况 *)
    - exists (el1 ++ el3), el4.
      split; [| rewrite H4, H5; apply app_assoc].
      right; exists i1, el1, el3; tauto.
    (* e12 err的情况 *)
    - exists el5, (el6 ++ el3 ++ el4).
      split; [| rewrite H4, H6, H5; apply app_assoc_reverse]; tauto.
Qed.

(** 下面把二元运算的情况汇总起来。*)
Instance EBinop_mono: forall op,
  Proper (erefine ==> erefine ==> erefine) (EBinop op).
Proof.
  unfold Proper, respectful.
  intros.
  destruct op.
  (** 布尔二元运算的情况 *)
  + split.
    - simpl; apply (or_sem_nrm_mono x y x0 y0); tauto.
    - apply or_sem_err_mono; tauto.
  + split.
    - apply and_sem_nrm_mono; tauto.
    - apply and_sem_err_mono; tauto.
  (** 大小比较的情况 *)
  + split.
    - apply cmp_sem_nrm_mono; tauto.
    - apply cmp_sem_err_mono; tauto.
  + split.
    - apply cmp_sem_nrm_mono; tauto.
    - apply cmp_sem_err_mono; tauto.
  + split.
    - apply cmp_sem_nrm_mono; tauto.
    - apply cmp_sem_err_mono; tauto.
  + split.
    - apply cmp_sem_nrm_mono; tauto.
    - apply cmp_sem_err_mono; tauto.
  + split.
    - apply cmp_sem_nrm_mono; tauto.
    - apply cmp_sem_err_mono; tauto.
  + split.
    - apply cmp_sem_nrm_mono; tauto.
    - apply cmp_sem_err_mono; tauto.
  (** 加减乘运算的情况 *)
  + split.
    - apply arith_sem1_nrm_mono; tauto.
    - apply arith_sem1_err_mono; tauto.
  + split.
    - apply arith_sem1_nrm_mono; tauto.
    - apply arith_sem1_err_mono; tauto.
  + split.
    - apply arith_sem1_nrm_mono; tauto.
    - apply arith_sem1_err_mono; tauto.
  (** 除法与取余的情况 *)
  + split.
    - apply arith_sem2_nrm_mono; tauto.
    - apply arith_sem2_err_mono; tauto.
  + split.
    - apply arith_sem2_nrm_mono; tauto.
    - apply arith_sem2_err_mono; tauto.
Qed.

(* not_sem能保持精化关系，nrm *)
Lemma not_sem_nrm_mono: forall (e1 e2: expr),
  e1 <<= e2 ->
  erefine_nrm (not_sem_nrm ⟦ e1 ⟧.(nrm))
              (not_sem_nrm ⟦ e2 ⟧.(nrm))
              (⟦ e2 ⟧.(err)).
Proof.
  intros.
  unfold erefine_nrm; intros s el i.
  unfold not_sem_nrm; intros.
  destruct H0 as (i1 & [? ?]).
  apply H.(nrm_erefine) in H0.
  destruct H0 as [? | (el1 & el2 & [? ?])].
  (* e2 nrm的情况 *)
  + left; exists i1; tauto.
  (* e2 err的情况 *)
  + right; exists el1, el2; tauto.
Qed.

(* not_sem能保持精化关系，err *)
Lemma not_sem_err_mono: forall (e1 e2: expr),
  e1 <<= e2 ->
  erefine_err ⟦ e1 ⟧.(err) ⟦ e2 ⟧.(err).
Proof.
  intros.
  unfold erefine_err; intros s el ?.
  apply H.(err_erefine) in H0; tauto.
Qed.

(* neg_sem能保持精化关系，nrm *)
Lemma neg_sem_nrm_mono: forall (e1 e2: expr),
  e1 <<= e2 ->
  erefine_nrm (neg_sem_nrm ⟦ e1 ⟧.(nrm))
              (neg_sem_nrm ⟦ e2 ⟧.(nrm))
              (⟦ e2 ⟧.(err) ∪ neg_sem_err ⟦ e2 ⟧.(nrm)).
Proof.
  intros.
  unfold erefine_nrm; intros s el i.
  unfold neg_sem_nrm, neg_sem_err; intros.
  destruct H0 as (i1 & [? ?]).
  apply H.(nrm_erefine) in H0.
  destruct H0 as [? | (el1 & el2 & [? ?])].
  (* e2 nrm的情况 *)
  + left; exists i1; tauto.
  (* e2 err的情况 *)
  + right; sets_unfold; exists el1, el2; tauto.
Qed.


(* neg_sem能保持精化关系，err *)
Lemma neg_sem_err_mono: forall (e1 e2: expr),
  e1 <<= e2 ->
  erefine_err (⟦ e1 ⟧.(err) ∪ neg_sem_err ⟦ e1 ⟧.(nrm))
              (⟦ e2 ⟧.(err) ∪ neg_sem_err ⟦ e2 ⟧.(nrm)).
Proof.
  intros.
  unfold erefine_err; intros s el.
  sets_unfold; unfold neg_sem_err; intros.
  destruct H0 as [? | (i & [? ?])].
  (* e1 err的情况 *)
  + apply H.(err_erefine) in H0.
    destruct H0 as (el1 & el2 & [? ?]).
    exists el1, el2; tauto.
  (* e1 nrm的情况 *)
  + apply H.(nrm_erefine) in H0.
    destruct H0 as [? | (el1 & el2 & [? ?])].
    (* e2 nrm的情况 *)
    - exists el, nil.
      split; [| rewrite app_nil_r; reflexivity].
      right; exists i; tauto.
    (* e2 err的情况 *)
    - exists el1, el2; tauto.
Qed.

(* 汇总一元运算的情况 *)
Instance EUnop_mono: forall op,
  Proper (erefine ==> erefine) (EUnop op).
Proof.
  unfold Proper, respectful.
  intros.
  destruct op.
  + split.
    - simpl; apply not_sem_nrm_mono; tauto.
    - simpl; apply not_sem_err_mono; tauto.
  + split.
    - apply neg_sem_nrm_mono; tauto.
    - apply neg_sem_err_mono; tauto.
Qed.

(* deref_sem能保持精化关系，nrm *)
Lemma deref_sem_nrm_mono: forall (e1 e2: expr),
e1 <<= e2 ->
erefine_nrm (deref_sem_nrm ⟦ e1 ⟧.(nrm))
            (deref_sem_nrm ⟦ e2 ⟧.(nrm))
            (⟦ e2 ⟧.(err) ∪ deref_sem_err ⟦ e2 ⟧.(nrm)).
Proof.
  intros.
  unfold erefine_nrm; intros s el i.
  unfold deref_sem_nrm; intros.
  destruct H0 as (i1 & [? ?]).
  apply H.(nrm_erefine) in H0.
  destruct H0 as [? | (el1 & el2 & [? ?])].
  (* e2 nrm的情况 *)
  + left; exists i1; tauto.
  (* e2 err的情况 *)
  + right; exists el1, el2. 
    sets_unfold; tauto.
Qed.

(* deref_sem能保持精化关系，err *)
Lemma deref_sem_err_mono: forall (e1 e2: expr),
  e1 <<= e2 ->
  erefine_err (⟦ e1 ⟧.(err) ∪ deref_sem_err ⟦ e1 ⟧.(nrm))
              (⟦ e2 ⟧.(err) ∪ deref_sem_err ⟦ e2 ⟧.(nrm)).
Proof.
  intros.
  unfold erefine_err, deref_sem_err; sets_unfold; intros s el ?.
  destruct H0.
  (* e1 err的情况 *)
  + apply H.(err_erefine) in H0.
    destruct H0 as (el1 & el2 & [? ?]).
    exists el1, el2; tauto.
  (* e1 nrm的情况 *)
  + destruct H0 as (i & [? ?]).
    apply H.(nrm_erefine) in H0.
    destruct H0 as [? | (el1 & el2 & [? ?])]; destruct H1.
    (* e2 nrm, 没有内存访问权限的情况 *)
    - exists el, nil.
      split; [| rewrite app_nil_r; tauto].
      right; exists i; tauto.
    (* e2 nrm, 有内存访问权限的情况 *)
    - exists el, nil.
      split; [| rewrite app_nil_r; tauto].
      right; exists i; tauto.
    (* e2 err, 没有内存访问权限的情况 *)
    - exists el1, el2; tauto.
    (* e2 err, 有内存访问权限的情况 *)
    - exists el1, el2; tauto.
Qed.

Instance EDeref_mono:
  Proper (erefine ==> erefine) EDeref.
Proof.
  unfold Proper, respectful.
  intros e1 e2 ?.
  split.
  + simpl; apply deref_sem_nrm_mono; tauto.
  + simpl; apply deref_sem_err_mono; tauto.
Qed.

(* write能保持精化关系 *)
Instance CWrite_mono:
  Proper (erefine ==> crefine) CWrite.
Proof.
  unfold Proper, respectful.
  intros e1 e2 ?.
  split; simpl.
  (* nrm *)
  + unfold crefine_nrm; intros s1 el s2.
    unfold writeint_sem_nrm; intros.
    destruct H0 as (i & el1 & [? [? ?] ]).
    apply H.(nrm_erefine) in H0.
    destruct H0 as [? | (el2 & el3 & [? ?])].
    (* e2 nrm的情况 *)
    - left; exists i, el1; tauto.
    (* e2 err的情况 *)
    - right; exists el2, (el3 ++ [outevent i]).
      split; [tauto | rewrite H1, H3; apply app_assoc_reverse].
  (* err *)
  + unfold crefine_err; intros s1 el ? .
    apply H.(err_erefine) in H0; apply H0.
  (* cinf *)
  + unfold crefine_cinf; intros s1 el.
    sets_unfold; tauto.
  (* ioinf *)
  + unfold crefine_ioinf; intros s1 el.
    sets_unfold; tauto.
Qed.

(* 赋值语句能保持精化关系 *)
Instance CAsgnVar_mono:
  Proper (eq ==> erefine ==> crefine) CAsgnVar.
Proof.
  unfold Proper, respectful.
  intros x1 x2 ? e1 e2 ?.
  split; simpl.
  (* nrm *)
  + unfold crefine_nrm; intros s1 el s2 ?.
    destruct H1 as (i & [? [? [? ?] ] ]).
    apply H0.(nrm_erefine) in H1.
    destruct H1.
    (* e2 nrm的情况 *)
    - left; exists i; rewrite <- H; tauto.
    (* e2 err的情况 *)
    - right; apply H1.
  (* err *)
  + unfold crefine_err; intros s1 el ?.
    apply H0.(err_erefine) in H1.
    apply H1.
  (* cinf *)
  + unfold crefine_cinf; intros s1 el.
    sets_unfold; tauto.
  (* ioinf *)
  + unfold crefine_ioinf; intros s1 el.
    sets_unfold; tauto.
Qed.

(* AsgnDeref能保持精化关系，nrm *)
Lemma CAsgnDeref_mono_nrm: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  crefine_nrm ⟦ (CAsgnDeref e11 e21) ⟧.(nrm)
              ⟦ (CAsgnDeref e12 e22) ⟧.(nrm)
              ⟦ (CAsgnDeref e12 e22) ⟧.(err).
Proof.
  simpl; intros e11 e12 e21 e22 ? ?.
  unfold crefine_nrm, asgn_deref_sem_nrm, asgn_deref_sem_err; intros s1 el s2 ?.
  sets_unfold.
  destruct H1 as (i1 & i2 & el1 & el2 & [? [? [? [? [? [? ?] ] ] ] ] ]).
  apply H.(nrm_erefine) in H2.
  apply H0.(nrm_erefine) in H3.
  destruct H2 as [? | (el3 & el4 & [? ?])]; destruct H3 as [? | (el5 & el6 & [? ?])].
  (* e12 e22都是nrm的情况 *)
  + left; exists i1, i2, el1, el2; tauto.
  (* e12 nrm, e22 err的情况 *)
  + right; exists (el1 ++ el5), el6.
    split; [| rewrite H1, H8; apply app_assoc].
    right; left; exists i1, el1, el5; tauto.
  (* e12 err, e22 nrm的情况 *)
  + right; exists el3, (el4 ++ el2).
    split; [tauto | rewrite H1, H8; apply app_assoc_reverse].
  (* e12 e22都是err的情况 *)
  + right; exists el3, (el4 ++ el2).
    split; [tauto | rewrite H1, H8, H9; apply app_assoc_reverse].
Qed.

(* AsgnDeref能保持精化关系，err *)
Lemma CAsgnDeref_mono_err: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  crefine_err ⟦ (CAsgnDeref e11 e21) ⟧.(err)
              ⟦ (CAsgnDeref e12 e22) ⟧.(err).
Proof.
  simpl; intros e11 e12 e21 e22 ? ?.
  unfold crefine_err, asgn_deref_sem_err; intros s1 el ?.
  destruct H1 as [? | [(i & el1 & el2 & [? [? [? ?] ] ]) | (i & [? ?])] ].
  (* e11 err的情况 *)
  + apply H.(err_erefine) in H1.
    destruct H1 as (el1 & el2 & [? ?]).
    exists el1, el2; tauto.
  (* e21 err的情况 *)
  + apply H.(nrm_erefine) in H2.
    apply H0.(err_erefine) in H4.
    destruct H4 as (el3 & el4 & [? ?]).
    destruct H2 as [? | (el5 & el6 & [? ?])].
    (* e12 nrm的情况 *)
    - exists (el1 ++ el3), el4.
      split; [| rewrite H1, H5; apply app_assoc].
      right; left; exists i, el1, el3; tauto.
    (* e12 err的情况 *)
    - exists el5, (el6 ++ el2).
      split; [tauto | rewrite H1, H6, H5; apply app_assoc_reverse].
  (* 没有访问权限的情况 *)
  + apply H.(nrm_erefine) in H1.
    destruct H1 as [? | (el1 & el2 & [? ?])].
    (* e12 nrm的情况 *)
    - exists el, nil.
      split; [| rewrite app_nil_r; tauto].
      right; right; exists i; tauto.
    (* e12 err的情况 *)
    - exists el1, el2; tauto.
Qed. 

(* AsgnDeref能保持精化关系，cinf *)
Lemma CAsgnDeref_mono_cinf: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  crefine_cinf ⟦ (CAsgnDeref e11 e21) ⟧.(cinf)
               ⟦ (CAsgnDeref e12 e22) ⟧.(cinf)
               ⟦ (CAsgnDeref e12 e22) ⟧.(err).
Proof.
  simpl; intros e11 e12 e21 e22 ? ?.
  unfold crefine_cinf, asgn_deref_sem_err; intros s1 el.
  sets_unfold; tauto.
Qed.

(* AsgnDeref能保持精化关系，ioinf *)
Lemma CAsgnDeref_mono_ioinf: forall (e11 e12 e21 e22: expr),
  e11 <<= e12 ->
  e21 <<= e22 ->
  crefine_ioinf ⟦ (CAsgnDeref e11 e21) ⟧.(ioinf)
                ⟦ (CAsgnDeref e12 e22) ⟧.(ioinf)
                ⟦ (CAsgnDeref e12 e22) ⟧.(err).
Proof.
  simpl; intros e11 e12 e21 e22 ? ?.
  unfold crefine_cinf, asgn_deref_sem_err; intros s1 el.
  sets_unfold; tauto.
Qed.

(* AsgnDeref能保持精化关系 *)
Instance CAsgnDeref_mono:
Proper (erefine ==> erefine ==> crefine) CAsgnDeref.
Proof.
  unfold Proper, respectful.
  intros e11 e12 ? e21 e22 ?.
  split.
  + apply (CAsgnDeref_mono_nrm e11 e12 e21 e22 H H0).
  + apply (CAsgnDeref_mono_err e11 e12 e21 e22 H H0).
  + apply (CAsgnDeref_mono_cinf e11 e12 e21 e22 H H0).
  + apply (CAsgnDeref_mono_ioinf e11 e12 e21 e22 H H0).
Qed.

(* CSeq能保持精化关系，nrm *)
Lemma CSeq_mono_nrm: forall (c11 c12 c21 c22: com),
  c11 <<= c12 ->
  c21 <<= c22 ->
  crefine_nrm ⟦ c11; c21 ⟧.(nrm) ⟦ c12; c22 ⟧.(nrm) ⟦ c12; c22 ⟧.(err).
Proof.
  simpl; intros c11 c12 c21 c22 ? ?.
  unfold crefine_nrm; intros s1 el s3.
  sets_unfold; intros.
  destruct H1 as (s2 & el1 & el2 & [? [? ?] ]).
  apply H.(nrm_crefine) in H2.
  apply H0.(nrm_crefine) in H3.
  destruct H2; destruct H3.
  (* c12 c22都是nrm的情况 *)
  + left; exists s2, el1, el2; tauto.
  (* c12 nrm, c22 err的情况 *)
  + destruct H3 as (el3 & el4 & [? ?]).
    right; exists (el1 ++ el3), el4.
    split; [| rewrite <- H1; rewrite H4; apply app_assoc].
    right; exists s2, el1, el3; tauto.
  (* c12 err, c22 nrm的情况 *)
  + destruct H2 as (el3 & el4 & [? ?]).
    right; exists el3, (el4 ++ el2).
    split; [tauto | rewrite <- H1; rewrite H4; apply app_assoc_reverse].
  (* c12 c22都是err的情况 *)
  + destruct H2 as (el3 & el4 & [? ?]).
    destruct H3 as (el5 & el6 & [? ?]).
    right; exists el3, (el4 ++ el5 ++ el6).
    split; [tauto | rewrite <- H1; rewrite H4, H5; apply app_assoc_reverse].
Qed.

(* CSeq能保持精化关系，err *)
Lemma CSeq_mono_err: forall (c11 c12 c21 c22: com),
  c11 <<= c12 ->
  c21 <<= c22 ->
  crefine_err ⟦ c11; c21 ⟧.(err) ⟦ c12; c22 ⟧.(err).
Proof.
  simpl; intros c11 c12 c21 c22 ? ?.
  unfold crefine_err; intros s1 el.
  sets_unfold; intros.
  destruct H1 as [? | (s2 & el1 & el2 & [? [? ?] ])].
  (* c11 err的情况 *)
  + apply H.(err_crefine) in H1.
    destruct H1 as (el1 & el2 & [? ?]).
    exists el1, el2; tauto.
  (* c21 err 的情况 *)
  + apply H.(nrm_crefine) in H2.
    apply H0.(err_crefine) in H3.
    destruct H3 as (el3 & el4 & [? ?]).
    destruct H2 as [? | (el5 & el6 & [? ?])].
    (* c12 nrm的情况 *)
    - exists (el1 ++ el3), el4.
      split; [| rewrite <- H1; rewrite H4; apply app_assoc].
      right; exists s2, el1, el3; tauto.
    (* c12 err的情况 *)
    - exists el5, (el6 ++ el3 ++ el4).
      split; [tauto | rewrite <- H1; rewrite H5, H4; apply app_assoc_reverse].
Qed.

(* CSeq能保持精化关系，cinf *)
Lemma CSeq_mono_cinf:  forall (c11 c12 c21 c22: com),
  c11 <<= c12 ->
  c21 <<= c22 ->
  crefine_cinf ⟦ c11; c21 ⟧.(cinf) ⟦ c12; c22 ⟧.(cinf) ⟦ c12; c22 ⟧.(err).
Proof.
  simpl; intros c11 c12 c21 c22 ? ?.
  unfold crefine_cinf; intros s1 el.
  sets_unfold; intros.
  destruct H1 as [? | (s2 & el1 & el2 & [? [? ?] ])].
  (* c11 cinf的情况 *)
  + apply H.(cinf_crefine) in H1.
    destruct H1 as [? | (el1 & el2 & [? ?])]; [tauto |].
    right; exists el1, el2; tauto.
  (* c21 cinf的情况 *)
  + apply H.(nrm_crefine) in H2.
    apply H0.(cinf_crefine) in H3.
    destruct H2; destruct H3.
    (* c12 nrm, c22 cinf的情况 *)
    - left; right.
      exists s2, el1, el2; tauto.
    (* c12 nrm, c22 err的情况 *)
    - destruct H3 as (el3 & el4 & [? ?]).
      right; exists (el1 ++ el3), el4.
      split; [| rewrite <- H1; rewrite H4; apply app_assoc].
      right; exists s2, el1, el3; tauto.
    (* c12 err, c22 cinf的情况 *)
    - destruct H2 as (el3 & el4 & [? ?]).
      right; exists el3, (el4 ++ el2).
      split; [tauto | rewrite <- H1; rewrite H4; apply app_assoc_reverse].
    (* c12 err, c22 err的情况 *)
    - destruct H2 as (el3 & el4 & [? ?]).
      destruct H3 as (el5 & el6 & [? ?]).
      right; exists el3, (el4 ++ el5 ++ el6).
      split; [tauto | rewrite <- H1; rewrite H4, H5; apply app_assoc_reverse].
Qed.

(* CSeq能保持精化关系，ioinf *)
Lemma CSeq_mono_ioinf:  forall (c11 c12 c21 c22: com),
  c11 <<= c12 ->
  c21 <<= c22 ->
  crefine_ioinf ⟦ c11; c21 ⟧.(ioinf) ⟦ c12; c22 ⟧.(ioinf) ⟦ c12; c22 ⟧.(err).
Proof.
  simpl; intros c11 c12 c21 c22 ? ?.
  unfold crefine_ioinf; intros s1 el.
  sets_unfold; intros.
  destruct H1 as [? | (s2 & el1 & es1 & [? [? ?] ])].
  (* c11 ioinf的情况 *)
  + apply H.(ioinf_crefine) in H1.
    destruct H1 as [? | (el1 & es & [? ?])]; [tauto |].
    right; exists el1, es; tauto.
  (* c21 ioinf的情况 *)
  + apply H.(nrm_crefine) in H2.
    apply H0.(ioinf_crefine) in H3.
    destruct H2 as [? | (el2 & el3 & [? ?])]; destruct H3 as [? | (el4 & es2 & [? ?])].
    (* c12 nrm, c22 ioinf的情况 *)
    - left; right; exists s2, el1, es1; tauto.
    (* c12 nrm, c22 err的情况 *)
    - right. exists (el1 ++ el4), es2.
      split; [right; exists s2, el1, el4; tauto |].
      rewrite <- H1; rewrite H4.
      symmetry; apply (StreamConn.stream_ACC_Assoc event).
    (* c12 err, c22 ioinf的情况 *)
    - right; exists el2, (StreamConn.stream_app el3 es1).
      split; [tauto |].
      rewrite <- H1; rewrite H4; apply (StreamConn.stream_ACC_Assoc event).
    (* c12 err, c22 err的情况 *)
    - right; exists el2, (StreamConn.stream_app el3 es1).
      split; [tauto |].
      rewrite <- H1; rewrite H4; apply (StreamConn.stream_ACC_Assoc event).
Qed.

(* CSeq能保持精化关系 *)
Instance CSeq_mono:
  Proper (crefine ==> crefine ==> crefine) CSeq.
Proof.
  unfold Proper, respectful.
  intros c11 c12 ? c21 c22 ?.
  split.
  + apply (CSeq_mono_nrm c11 c12 c21 c22 H H0).
  + apply (CSeq_mono_err c11 c12 c21 c22 H H0).
  + apply (CSeq_mono_cinf c11 c12 c21 c22 H H0).
  + apply (CSeq_mono_ioinf c11 c12 c21 c22 H H0).
Qed.

(* test_true能保持精化关系 *)
Lemma test_true_mono: forall (e1 e2: expr),
  e1 <<= e2 ->
  crefine_nrm (test_true ⟦ e1 ⟧) (test_true ⟦ e2 ⟧) (⟦ e2 ⟧.(err)).
Proof.
  intros.
  unfold crefine_nrm, test_true; sets_unfold; intros s1 el s2 ?.
  destruct H0 as [(i1 & [? ?]) ?].
  apply H.(nrm_erefine) in H0.
  destruct H0.
  (* e2 nrm的情况 *)
  + left; split; [| tauto].
    exists i1; tauto.
  (* e2 err的情况 *)
  + destruct H0 as (el1 & el2 & [? ?]).
    right; exists el1, el2; tauto.
Qed.

(* test_false能保持精化关系 *)
Lemma test_false_mono: forall (e1 e2: expr),
  e1 <<= e2 ->
  crefine_nrm (test_false ⟦ e1 ⟧) (test_false ⟦ e2 ⟧) (⟦ e2 ⟧.(err)).
Proof.
  intros.
  unfold crefine_nrm, test_false; sets_unfold; intros s1 el s2 ?.
  destruct H0.
  apply H.(nrm_erefine) in H0.
  destruct H0; [left; tauto |].
  destruct H0 as (el1 & el2 & [? ?]).
  right; exists el1, el2; tauto.
Qed.

(* CIf能保持精化关系, nrm *)
Lemma CIf_mono_nrm:  forall (e1 e2: expr) (c11 c12 c21 c22: com),
  e1 <<= e2 ->
  c11 <<= c12 ->
  c21 <<= c22 ->
  crefine_nrm ⟦ if e1 then { c11 } else { c21 } ⟧.(nrm)
              ⟦ if e2 then { c12 } else { c22 } ⟧.(nrm)
              ⟦ if e2 then { c12 } else { c22 } ⟧.(err).
Proof.
  simpl; intros e1 e2 c11 c12 c21 c22 ? ? ?.
  unfold crefine_nrm; intros s1 el s3.
  sets_unfold; intros.
  destruct H2 as [(s2 & el1 & el2 & [? [? ?] ]) | (s2 & el1 & el2 & [? [? ?] ])].
  (* e1 test_true的情况 *)
  + apply (test_true_mono e1 e2 H) in H3.
    apply H0.(nrm_crefine) in H4.
    destruct H3 as [? | (el3 & el4 & [? ?])]; destruct H4 as [? | (el5 & el6 & [? ?])].
    (* e2 test_true, c12 nrm的情况 *)
    - left; left; exists s2, el1, el2; tauto.
    (* e2 test_true, c12 err的情况 *)
    - right; exists (el1 ++ el5), el6.
      split; [| rewrite <- H2; rewrite H5; apply app_assoc].
      left; right; exists s2, el1, el5; tauto.
    (* e2 err, e12 nrm的情况 *)
    - right; exists el3, (el4 ++ el2).
      split; [tauto | rewrite <- H2; rewrite H5; apply app_assoc_reverse].
    (* e2 err, c12 err的情况 *)
    - right; exists el3, (el4 ++ el2).
      split; [tauto | rewrite <- H2; rewrite H6, H5; apply app_assoc_reverse].
  (* e1 test_false的情况 *)
  + apply (test_false_mono e1 e2 H) in H3.
    apply H1.(nrm_crefine) in H4.
    destruct H3 as [? | (el3 & el4 & [? ?])]; destruct H4 as [? | (el5 & el6 & [? ?])].
    (* e2 test_false, c22 nrm的情况 *)
    - left; right; exists s2, el1, el2; tauto.
    (* e2 test_false, c22 err的情况 *)
    - right; exists (el1 ++ el5), el6.
      split; [| rewrite <- H2; rewrite H5; apply app_assoc].
      right; exists s2, el1, el5; tauto.
    (* e2 err, c22 nrm的情况 *)
    - right; exists el3, (el4 ++ el2).
      split; [tauto | rewrite <- H2; rewrite H5; apply app_assoc_reverse].
    (* e2 err, c22 err的情况s *)
    - right; exists el3, (el4 ++ el2).
      split; [tauto | rewrite <- H2; rewrite H5, H6; apply app_assoc_reverse].
Qed.

(* CIf能保持精化关系, err *)
Lemma CIf_mono_err:  forall (e1 e2: expr) (c11 c12 c21 c22: com),
  e1 <<= e2 ->
  c11 <<= c12 ->
  c21 <<= c22 ->
  crefine_err ⟦ if e1 then { c11 } else { c21 } ⟧.(err)
              ⟦ if e2 then { c12 } else { c22 } ⟧.(err).
Proof.
  simpl; intros e1 e2 c11 c12 c21 c22 ? ? ?.
  unfold crefine_err; intros s1 el.
  sets_unfold; intros.
  destruct H2 as [ [? | (s2 & el1 & el2 & [? [? ?] ])] | (s2 & el1 & el2 & [? [? ?] ])].
  (* e1 err的情况 *)
  + apply H.(err_erefine) in H2.
    destruct H2 as (el1 & el2 & [? ?]).
    exists el1, el2; tauto.
  (* c11 err的情况 *)
  + apply (test_true_mono e1 e2 H) in H3.
    apply H0.(err_crefine) in H4.
    destruct H4 as (el3 & el4 & [? ?]).
    destruct H3 as [? | (el5 & el6 & [? ?])].
    (* e2 test_true的情况 *)
    - exists (el1 ++ el3), el4.
      split; [| rewrite <- H2; rewrite H5; apply app_assoc].
      left; right; exists s2, el1, el3; tauto.
    (* e2 err的情况 *)
    - exists el5, (el6 ++ el2).
      split; [tauto | rewrite <- H2; rewrite H5, H6; apply app_assoc_reverse].
  (* c21 err的情况 *)
  + apply (test_false_mono e1 e2 H) in H3.
    apply H1.(err_crefine) in H4.
    destruct H4 as (el3 & el4 & [? ?]).
    destruct H3 as [? | (el5 & el6 & [? ?])].
    (* e2 test_false的情况 *)
    - exists (el1 ++ el3), el4.
      split; [| rewrite <- H2; rewrite H5; apply app_assoc].
      right; exists s2, el1, el3; tauto.
    (* e2 err的情况 *)
    - exists el5, (el6 ++ el2).
      split; [tauto | rewrite <- H2; rewrite H5, H6; apply app_assoc_reverse].
Qed.

(* CIf能保持精化关系, cinf *)
Lemma CIf_mono_cinf:  forall (e1 e2: expr) (c11 c12 c21 c22: com),
  e1 <<= e2 ->
  c11 <<= c12 ->
  c21 <<= c22 ->
  crefine_cinf ⟦ if e1 then { c11 } else { c21 } ⟧.(cinf)
               ⟦ if e2 then { c12 } else { c22 } ⟧.(cinf)
               ⟦ if e2 then { c12 } else { c22 } ⟧.(err).
Proof.
  simpl; intros e1 e2 c11 c12 c21 c22 ? ? ?.
  unfold crefine_cinf; intros s1 el.
  sets_unfold; intros.
  destruct H2 as [(s2 & el1 & el2 & [? [? ?] ]) | (s2 & el1 & el2 & [? [? ?] ])].
  (* e1 test_true的情况 *)
  + apply (test_true_mono e1 e2 H) in H3.
    apply H0.(cinf_crefine) in H4.
    destruct H3 as [? | (el3 & el4 & [? ?])]; destruct H4 as [? | (el5 & el6 & [? ?])].
    (* e2 test_true, c12 cinf的情况 *)
    - left; left; exists s2, el1, el2; tauto.
    (* e2 test_true, c12 err的情况 *)
    - right; exists (el1 ++ el5), el6.
      split; [| rewrite <- H2; rewrite H5; apply app_assoc].
      left; right; exists s2, el1, el5; tauto.
    (* e2 err, c12 cinf的情况 *)
    - right; exists el3, (el4 ++ el2).
      split; [tauto | rewrite <- H2; rewrite H5; apply app_assoc_reverse].
    (* e2 err, e12 err的情况 *)
    - right; exists el3, (el4 ++ el2).
      split; [tauto | rewrite <- H2; rewrite H5, H6; apply app_assoc_reverse].
  (* e1 test_false的情况 *)
  + apply (test_false_mono e1 e2 H) in H3.
    apply H1.(cinf_crefine) in H4.
    destruct H3 as [? | (el3 & el4 & [? ?])]; destruct H4 as [? | (el5 & el6 & [? ?])].
    (* e2 test_false, c22 cinf的情况 *)
    - left; right; exists s2, el1, el2; tauto.
    (* e2 test_false, c22 err的情况 *)
    - right; exists (el1 ++ el5), el6.
      split; [| rewrite <- H2; rewrite H5; apply app_assoc].
      right; exists s2, el1, el5; tauto.
    (* e2 err, c22 cinf的情况 *)
    - right; exists el3, (el4 ++ el2).
      split; [tauto | rewrite <- H2; rewrite H5; apply app_assoc_reverse].
    (* e2 err, c22 err的情况 *)
    - right; exists el3, (el4 ++ el2).
      split; [tauto | rewrite <- H2; rewrite H5, H6; apply app_assoc_reverse].
Qed.

(* CIf能保持精化关系, ioinf *)
Lemma CIf_mono_ioinf:  forall (e1 e2: expr) (c11 c12 c21 c22: com),
  e1 <<= e2 ->
  c11 <<= c12 ->
  c21 <<= c22 ->
  crefine_ioinf ⟦ if e1 then { c11 } else { c21 } ⟧.(ioinf)
                ⟦ if e2 then { c12 } else { c22 } ⟧.(ioinf)
                ⟦ if e2 then { c12 } else { c22 } ⟧.(err).
Proof.
  simpl; intros e1 e2 c11 c12 c21 c22 ? ? ?.
  unfold crefine_ioinf; intros s1 el.
  sets_unfold; intros.
  destruct H2 as [(s2 & el1 & es1 & [? [? ?] ]) | (s2 & el1 & es1 & [? [? ?] ])].
  (* e1 test_true的情况 *)
  + apply (test_true_mono e1 e2 H) in H3.
    apply H0.(ioinf_crefine) in H4.
    destruct H3 as [? | (el2 & el3 & [? ?])]; destruct H4 as [? | (el4 & es2 & [? ?])].
    (* e2 test_true, c12 ioinf的情况 *)
    - left; left; exists s2, el1, es1; tauto.
    (* e2 test_true, c12 err的情况 *)
    - right; exists (el1 ++ el4), es2.
      split; [| rewrite <- H2; rewrite H5; symmetry; apply (StreamConn.stream_ACC_Assoc event)].
      left; right; exists s2, el1, el4; tauto.
    (* e2 err, c12 ioinf的情况 *)
    - right. exists el2, (StreamConn.stream_app el3 es1).
      split; [tauto | rewrite <- H2; rewrite H5; apply (StreamConn.stream_ACC_Assoc event)].
    (* e2 err, c12 err的情况 *)
    - right. exists el2, (StreamConn.stream_app el3 es1).
      split; [tauto | rewrite <- H2; rewrite H5, H6; apply (StreamConn.stream_ACC_Assoc event)].
  (* e1 test_false的情况 *)
  + apply (test_false_mono e1 e2 H) in H3.
    apply H1.(ioinf_crefine) in H4.
    destruct H3 as [? | (el2 & el3 & [? ?])]; destruct H4 as [? | (el4 & es2 & [? ?])].
    (* e2 test_false, c22 ioinf的情况 *)
    - left; right; exists s2, el1, es1; tauto.
    (* e2 test_false, c22 err的情况 *)
    - right; exists (el1 ++ el4), es2.
      split; [| rewrite <- H2; rewrite H5; symmetry; apply (StreamConn.stream_ACC_Assoc event)].
      right; exists s2, el1, el4; tauto.
    (* e2 err, c22 ioinf的情况 *)
    - right; exists el2, (StreamConn.stream_app el3 es1).
      split; [tauto | rewrite <- H2; rewrite H5; apply (StreamConn.stream_ACC_Assoc event)].
    (* e2 err, c22 err的情况 *)
    - right; exists el2, (StreamConn.stream_app el3 es1).
      split; [tauto | rewrite <- H2; rewrite H5, H6; apply (StreamConn.stream_ACC_Assoc event)].
Qed.

(* CIf能保持精化关系 *)
Instance CIf_mono:
  Proper (erefine ==> crefine ==> crefine ==> crefine) CIf.
Proof.
  unfold Proper, respectful.
  intros e1 e2 ? c11 c12 ? c21 c22 ?.
  split.
  + apply (CIf_mono_nrm e1 e2 c11 c12 c21 c22 H H0 H1).
  + apply (CIf_mono_err e1 e2 c11 c12 c21 c22 H H0 H1).
  + apply (CIf_mono_cinf e1 e2 c11 c12 c21 c22 H H0 H1).
  + apply (CIf_mono_ioinf e1 e2 c11 c12 c21 c22 H H0 H1).
Qed.

(* event_list拼接的辅助函数 *)
Lemma triple_asso_list:
  forall (el1 el2 el3 el4: event_list),
    el1 ++ el2 ++ el3 ++ el4 = (el1 ++ el2 ++ el3) ++ el4.
Proof.
  intros.
  pose proof (app_assoc el1 (el2 ++ el3) el4).
  pose proof (app_assoc el2 el3 el4).
  rewrite <- H0 in H.
  apply H.
Qed.

(* event_list拼接的辅助函数 *)
Lemma two_in_four_asso_list:
  forall (el1 el2 el3 el4: event_list),
    el1 ++ (el2 ++ el3) ++ el4 = (el1 ++ el2) ++ el3 ++ el4.
Proof.
  intros.
  pose proof (app_assoc_reverse el2 el3 el4).
  rewrite H.
  pose proof (app_assoc el1 el2 el3).
  pose proof (triple_asso_list el1 el2 el3 el4).
  pose proof (app_assoc (el1 ++ el2) el3 el4).
  rewrite H1, H0, H2; reflexivity.
Qed.

Lemma boundedLB_nrm_mono_aux:
  forall (e1 e2: expr) (c1 c2: com) n,
    e1 <<= e2 ->
    c1 <<= c2 ->
    crefine_nrm (boundedLB_nrm ⟦ e1 ⟧ ⟦ c1 ⟧ n) (boundedLB_nrm ⟦ e2 ⟧ ⟦ c2 ⟧ n) (boundedLB_err ⟦ e2 ⟧ ⟦ c2 ⟧ n).
Proof.
  intros.
  unfold crefine_nrm.
  induction n; simpl.
  + sets_unfold; tauto.
  + sets_unfold; intros s1 el s2 ?.
    destruct H1.
    - destruct H1 as (s3 & el1 & el2 & [? [? (s4 & el3 & el4 & [? [? ?] ])] ]).
      specialize (IHn s4 el4 s2 H5).
      pose proof (test_true_mono e1 e2 H); unfold crefine_nrm in H6.
      specialize (H6 s1 el1 s3 H2).
      apply H0.(nrm_crefine) in H4.
      destruct IHn as [? | (el5 & el6 & [? ?])]; destruct H4 as [? | (el7 & el8 & [? ?])]; destruct H6 as [? | (el9 & el10 & [? ?])].
      * left; left; exists s3, el1, el2.
        split; [tauto |].
        split; [tauto | exists s4, el3, el4; tauto].
      * right; exists el9, (el10 ++ el2).
        split; [right; tauto | rewrite <- H1; rewrite H8; apply app_assoc_reverse].
      * right; exists (el1 ++ el7), (el8 ++ el4).
        split; [left; exists s3, el1, el7; tauto | rewrite <- H1, <- H3, H8].
        rewrite (app_assoc_reverse el7 el8 el4); apply app_assoc.
      * right; exists el9, (el10 ++ el2).
        split; [tauto | rewrite <- H1, H9; apply app_assoc_reverse].
      * right; exists (el1 ++ el3 ++ el5), el6.
        split; [| rewrite <- H1, <- H3, H8; apply (triple_asso_list el1 el3 el5 el6)].
        left; exists s3, el1, (el3 ++ el5).
        split; [tauto |].
        split; [tauto | left; exists s4, el3, el5; tauto].
      * right; exists el9, (el10 ++ el2).
        split; [tauto | rewrite <- H1, H9; apply app_assoc_reverse].
      * right; exists (el1 ++ el7), (el8 ++ el4).
        split; [| rewrite <- H1, <- H3, H9; apply (two_in_four_asso_list el1 el7 el8 el4)].
        left; exists s3, el1, el7; tauto.
      * right; exists el9, (el10 ++ el2).
        split; [tauto | rewrite <- H1, H10; apply app_assoc_reverse].
    - pose proof (test_false_mono e1 e2 H); unfold crefine_nrm in H2.
      specialize (H2 s1 el s2 H1).
      destruct H2 as [? | (el1 & el2 & [? ?])]; [tauto |].
      right; exists el1, el2; tauto.
Qed.

Lemma boundedLB_err_mono_aux:
  forall (e1 e2: expr) (c1 c2: com) n,
    e1 <<= e2 ->
    c1 <<= c2 ->
    crefine_err (boundedLB_err ⟦ e1 ⟧ ⟦ c1 ⟧ n) (boundedLB_err ⟦ e2 ⟧ ⟦ c2 ⟧ n).
Proof.
  intros.
  unfold crefine_err.
  induction n; simpl.
  + sets_unfold; tauto.
  + sets_unfold; intros s1 el ?.
    destruct H1 as [(s2 & el1 & el2 & [? [? [(s3 & el3 & el4 & [? [? ?] ])| ?] ] ]) | ?].
    - pose proof (test_true_mono e1 e2 H); unfold crefine_nrm in H6.
      specialize (H6 s1 el1 s2 H2).
      apply H0.(nrm_crefine) in H4.
      specialize (IHn s3 el4 H5).
      destruct IHn as (el5 & el6 & [? ?]).
      destruct H4 as [? | (el7 & el8 & [? ?])]; destruct H6 as [? | (el9 & el10 & [? ?])].
      * exists (el1 ++ el3 ++ el5), el6.
        split; [| rewrite <- H1, <- H3, H8; apply (triple_asso_list el1 el3 el5 el6)].
        left; exists s2, el1, (el3 ++ el5).
        split; [tauto |].
        split; [tauto | left; exists s3, el3, el5; tauto].
      * exists el9, (el10 ++ el2).
        split; [tauto | rewrite <- H1, H9; apply app_assoc_reverse].
      * exists (el1 ++ el7), (el8 ++ el4).
        split; [| rewrite <- H1, <- H3, H9; apply (two_in_four_asso_list el1 el7 el8 el4)].
        left; exists s2, el1, el7; tauto.
      * exists el9, (el10 ++ el2).
        split; [tauto | rewrite <- H1, H10; apply app_assoc_reverse].
    - pose proof (test_true_mono e1 e2 H); unfold crefine_nrm in H4.
      specialize (H4 s1 el1 s2 H2).
      destruct H4 as [? | (el3 & el4 & [? ?])].
      apply H0.(err_crefine) in H3.
      destruct H3 as (el5 & el6 & [? ?]).
      * exists (el1 ++ el5), el6.
        split; [| rewrite <- H1, H5; apply app_assoc].
        left; exists s2, el1, el5; tauto.
      * exists el3, (el4 ++ el2).
        split; [tauto | rewrite <- H1, H5; apply app_assoc_reverse].
    - apply H.(err_erefine) in H1.
      destruct H1 as (el1 & el2 & [? ?]).
      exists el1, el2; tauto.
Qed.

Lemma boundedLb_err_included_aux:
  forall (D1: EDenote) (D2: CDenote) (n1: nat),
  (boundedLB_err D1 D2 n1) ⊆ (boundedLB_err D1 D2 (S n1)).
Proof.
  intros.
  simpl.
  rewrite Rels_concat_union_distr_l.
  induction n1; simpl.
  + sets_unfold; tauto.
  + sets_unfold; intros s1 el ?.
    sets_unfold in IHn1.
    destruct H as [(s2 & el1 & el2 & [? [? [(s3 & el3 & el4 & [? [? ?] ]) | ?] ] ]) | ?]; [| | tauto].
    - specialize (IHn1 s3 el4 H3).
      destruct IHn1 as [ [(s4 & el5 & el6 & [? [? (s5 & el7 & el8 & [? [? ?] ])] ]) | (s4 & el5 & el6 & [? [? ?] ])] | ?].
      * left; left; exists s2, el1, el2.
        split; [tauto |]; split; [tauto |].
        exists s3, el3, el4.
        split; [tauto |]; split; [tauto |].
        left; exists s4, el5, el6.
        split; [tauto |]; split; [tauto |].
        left; exists s5, el7, el8; tauto.
      * left; left; exists s2, el1, el2.
        split; [tauto |]; split; [tauto |].
        exists s3, el3, el4.
        split; [tauto |]; split; [tauto |].
        left; exists s4, el5, el6.
        split; [tauto |]; tauto.
      * left; left; exists s2, el1, el2.
        split; [tauto |]; split; [tauto |].
        exists s3, el3, el4.
        split; [tauto |]; tauto.
    - left; right; exists s2, el1, el2; tauto.
Qed.

Lemma Sets_complement_indexed_union:
  forall {A B I: Type} (Xs: I -> A -> B -> Prop),
    Sets.complement (⋃ Xs) ==
    ⋂ (fun n => Sets.complement (Xs n)).
Proof.
  intros.
  sets_unfold.
  split.
  + apply not_ex_all_not.
  + apply all_not_not_ex.
Qed.

Definition noerrorLB (D1: EDenote) (D2: CDenote): State -> event_list -> Prop :=
  Sets.complement (⋃ (boundedLB_err D1 D2)).

Lemma iter_err_fact:
  forall (D1: EDenote) (D2: CDenote),
    test_true D1 ∘ D2.(nrm) ∘ ⋃ (boundedLB_err D1 D2) ⊆
    ⋃ (boundedLB_err D1 D2).
Proof.
  intros.
  rewrite ! Rels_concat_indexed_union_distr_l.
  apply Sets_indexed_union_included; intros n.
  rewrite <- (Sets_included_indexed_union _ _ (S n)).
  simpl.
  sets_unfold; intros.
  destruct H.
  destruct H.
  destruct H.
  left.
  exists x.
  exists x0.
  exists x1.
  tauto.
Qed.

Lemma Rels_concat_excluding_r:
  forall
    {A B: Type}
    (R: A -> B -> Prop)
    (S T: B -> Prop),
    (R ∘ S) ∩ Sets.complement (R ∘ T) ⊆
    R ∘ (S ∩ Sets.complement T).
Proof.
  intros.
  Sets_unfold; intros a.
  intros [ [b [? ?] ] ?].
  exists b.
  split; [tauto |].
  split; [tauto |].
  assert (T b -> exists b : B, R a b /\ T b); [| tauto].
  clear H1; intros.
  exists b; tauto.
Qed.

Lemma noerrorLB_fact1:
  forall (D1: EDenote) (D2: CDenote),
    D1.(err) ∩ noerrorLB D1 D2 == ∅.
Proof.
  intros.
  unfold noerrorLB.
  rewrite Sets_complement_indexed_union.
  apply Sets_equiv_Sets_included.
  split; [| apply Sets_empty_included].
  rewrite (Sets_indexed_intersect_included _ _ (S O)).
  simpl.
  sets_unfold; intros s.
  tauto.
Qed.

Lemma noerrorLB_fact2:
  forall (D1: EDenote) (D2: CDenote),
    (test_true D1 ∘ D2.(err)) ∩ noerrorLB D1 D2 == ∅.
Proof.
  intros.
  unfold noerrorLB.
  rewrite Sets_complement_indexed_union.
  apply Sets_equiv_Sets_included.
  split; [| apply Sets_empty_included].
  rewrite (Sets_indexed_intersect_included _ _ (S O)).
  simpl.
  sets_unfold; intros.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  left.
  exists x.
  exists x0.
  exists x1.
  tauto.
Qed.

(*辅助函数，用于转换证明为逆否命题*)
Theorem contrapositive : forall (P Q : Prop),
  (~P -> ~Q) -> (Q -> P).
Proof.
  intros P Q H.
  tauto.
Qed.

Theorem contrapositive1 : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H.
  tauto.
Qed.

Lemma double_neg_elim : forall P : Prop, P -> ~~P.
Proof.
  intros P HP.
  intro HNNP.
  apply HNNP.
  assumption. 
Qed.

Lemma double_neg_elim1 : forall P : Prop, ~~P -> P.
Proof.
  intros P H.
  apply NNPP. (* 法则：双否定消除 *)
  assumption.
Qed.

(*辅助函数，用于证明若是在该程序状态和eventlist的情况下是noerror的，那么外面再复合上一层test_true和循环体那么同样是noerror的*)
Lemma iter_noerr_fact:
  forall (D1: EDenote) (D2: CDenote) (s1 s2 s3: State)
   (el1 el2 el3: event_list),
    test_true D1 s1 el1 s2 -> D2.(nrm) s2 el2 s3 ->
    noerrorLB D1 D2 s1 (el1 ++ el2 ++ el3) -> noerrorLB D1 D2 s3 el3.
Proof.
  intros ? ? ? ? ? ? ? ? ? ?.
  unfold noerrorLB in *. sets_unfold.
  apply contrapositive1.
  intros.
  destruct H1.
  exists (S x).
  simpl.
  sets_unfold.
  left.
  exists s2. exists el1. exists (el2 ++ el3). 
  split; [tauto|].
  split; [tauto|].
  left.
  exists s3. exists el2. exists el3. tauto.
Qed.

Lemma lst_aux:
  forall (el1 el2 el: event_list),
    el1 ++ el2 = el -> el = [] -> el1 = [] /\ el2 = [].
Proof.
  intros.
  rewrite H0 in H.
  apply app_eq_nil.
  tauto.
Qed.    

(*证明在没有io的情况下，若X满足e1，c1的is_cinf_noio，那么去除掉可能会在e2，c2中产生错误的，剩下来的一定是符合is_cinf_noio e2 c2的，本处的证明和未引入event
 list的时候类似*)
Lemma cinf_noio_mono_aux:
  forall (e1 e2: expr) (c1 c2: com) (X: State -> event_list -> Prop),
    e1 <<= e2 ->
    c1 <<= c2 ->
    ((is_cinf_noio ⟦ e1 ⟧ ⟦ c1 ⟧)) (test_noio X) ->
    ((is_cinf_noio ⟦ e2 ⟧ ⟦ c2 ⟧)) (test_noio (X ∩ noerrorLB ⟦ e2 ⟧ ⟦ c2 ⟧)). 
Proof.
  unfold is_cinf_noio, test_noio; intros.
  sets_unfold in H1; sets_unfold.
  intros s1 el ?.
  destruct H2. destruct H2.
  assert (X s1 el /\ el = []) as H_aux. {
    tauto.
  }
  pose proof (H1 s1 el H_aux).
  destruct H5 as (s2 & el1 & el2 & [? [? [(s3 & el3 & el4 & [? [? ?] ]) | ?] ] ]).
  (*根据具体的cinf的情况分类讨论*)
  + apply H0.(nrm_crefine) in H8.
    apply (test_true_mono e1 e2 H) in H6.
    destruct H6 as [? | (el5 & el6 & [? ?])]; destruct H8 as [? | (el7 & el8 & [? ?])].
    - exists s2, el1, el2.
      split; [tauto |]; split; [tauto |].
      left; exists s3, el3, el4.
      pose proof (iter_noerr_fact ⟦ e2 ⟧ ⟦ c2 ⟧ s1 s2 s3 el1 el3 el4 H6 H8).
      rewrite H7, H5 in H10; specialize (H10 H4).
      tauto.
    - pose proof (noerrorLB_fact2 ⟦ e2 ⟧ ⟦ c2 ⟧).
      sets_unfold in H11.
      specialize (H11 s1 (el1 ++ el7)).
      destruct H11. clear H12.
      destruct H11.
      pose proof lst_aux el1 el2 el H5 H3.
      destruct H11.
      pose proof lst_aux el3 el4 el2 H7 H12.
      destruct H13.
      symmetry in H10.
      pose proof lst_aux el7 el8 el3 H10 H13.
      destruct H15.
      rewrite H11. rewrite H15. rewrite H3 in H4.
      simpl.
      split; [|tauto].
      exists s2. exists el1. exists el7.
      rewrite H11. rewrite H15. simpl.
      split; [tauto|].
      rewrite H11 in H6. rewrite H15 in H8.
      tauto.
    - pose proof (noerrorLB_fact1 ⟦ e2 ⟧ ⟦ c2 ⟧).
      sets_unfold in H11; specialize (H11 s1 el5).
      destruct H11.
      destruct H11.
      split; [tauto |].
      pose proof lst_aux el1 el2 el H5 H3.
      destruct H11.
      symmetry in H10.
      pose proof lst_aux el5 el6 el1 H10 H11.
      destruct H14.
      rewrite H3 in H4. rewrite H14. tauto.
    - pose proof (noerrorLB_fact1 ⟦ e2 ⟧ ⟦ c2 ⟧).
      sets_unfold in H12; specialize (H12 s1 el5).
      destruct H12.
      destruct H12.
      split; [tauto |].
      pose proof lst_aux el1 el2 el H5 H3.
      destruct H12.
      symmetry in H10.
      pose proof lst_aux el5 el6 el1 H10 H12.
      destruct H15.
      rewrite H3 in H4. rewrite H15. tauto.
  + apply H0.(cinf_crefine) in H7. 
    apply (test_true_mono e1 e2 H) in H6.
    destruct H6 as [? | (el5 & el6 & [? ?])]; destruct H7 as [? | (el7 & el8 & [? ?])].
    - exists s2, el1, el2; tauto.
    - pose proof (noerrorLB_fact2 ⟦ e2 ⟧ ⟦ c2 ⟧).
      sets_unfold in H9.
      specialize (H9 s1 (el1 ++ el7)).
      destruct H9.
      destruct H9.
      pose proof lst_aux el1 el2 el H5 H3.
      destruct H9. symmetry in H8.
      pose proof lst_aux el7 el8 el2 H8 H11.
      destruct H12.
      subst el1. subst el. subst el7. simpl.
      split; [|tauto].
      exists s2. exists el8. exists el8. subst el8. simpl.
      tauto.
    - pose proof (noerrorLB_fact1 ⟦ e2 ⟧ ⟦ c2 ⟧).
      sets_unfold in H9; specialize (H9 s1 el5).
      destruct H9.
      destruct H9.
      pose proof lst_aux el1 el2 el H5 H3. destruct H9.
      symmetry in H8.
      pose proof lst_aux el5 el6 el1 H8 H9. destruct H12.
      subst el5. subst el. tauto.
    - pose proof (noerrorLB_fact1 ⟦ e2 ⟧ ⟦ c2 ⟧).
      sets_unfold in H10; specialize (H10 s1 el5).
      destruct H10.
      destruct H10.
      pose proof lst_aux el1 el2 el H5 H3. destruct H10.
      symmetry in H8.
      pose proof lst_aux el5 el6 el1 H8 H10. destruct H13.
      subst el5. subst el. tauto.
Qed.

(*证明noio的情况下是满足crefine的*)
Lemma is_cinf_noio_ref:
  forall (e1 e2: expr) (c1 c2: com),
    e1 <<= e2 ->
    c1 <<= c2 ->
    crefine_cinf (test_noio (Sets.general_union (is_cinf_noio ⟦ e1 ⟧ ⟦ c1 ⟧))) (test_noio(Sets.general_union (is_cinf_noio ⟦ e2 ⟧ ⟦ c2 ⟧))) (test_noio(⋃ (boundedLB_err ⟦ e2 ⟧ ⟦ c2 ⟧))) .
Proof.
  unfold crefine_cinf, test_noio; sets_unfold.
  intros.  
  destruct H1. destruct H1. destruct H1.
  (*本处是对noio的程序语句进行讨论，首先对x增加noio的条件以使用上面证明的结论。由于是加条件所以这边的证明是比较自然的*)
  assert (is_cinf_noio ⟦ e1 ⟧ ⟦ c1 ⟧ (test_noio x)). {
    unfold test_noio.
    unfold is_cinf_noio. sets_unfold.
    unfold is_cinf_noio in H1. sets_unfold in H1.
    intros. destruct H4. specialize (H1 a a0 H4). 
    destruct H1. destruct H1. destruct H1. destruct H1. destruct H6. 
    exists x0. exists x1. exists x2. 
    split; [tauto|]. split; [tauto|].
    destruct H7. 
    + pose proof lst_aux x1 x2 a0 H1 H5. destruct H8.
      destruct H7. destruct H7. destruct H7. destruct H7.
      pose proof lst_aux x4 x5 x2 H7 H9. destruct H11. destruct H10.
      left. exists x3. exists x4. exists x5.
      tauto.
    + right. tauto.
  }
  pose proof cinf_noio_mono_aux e1 e2 c1 c2 x H H0 H4.
  unfold test_noio in H5.
  unfold is_cinf_noio in *.
  sets_unfold in H5.
  (*要对x进行分类讨论，总归是要么有error要么没有*)
  assert (x == (x ∩ noerrorLB ⟦ e2 ⟧ ⟦ c2 ⟧) ∪ (x ∩ (⋃ (boundedLB_err ⟦ e2 ⟧ ⟦ c2 ⟧)))). {
    unfold noerrorLB.
    rewrite <- Sets_intersect_union_distr_l.
    assert ((Sets.complement (⋃ (boundedLB_err ⟦ e2 ⟧ ⟦ c2 ⟧))
    ∪ ⋃ (boundedLB_err ⟦ e2 ⟧ ⟦ c2 ⟧)) == Sets.full). {
      sets_unfold.
      intros.
      split.
      + intros. tauto.
      + intros. 
        pose proof classic (exists i : nat, boundedLB_err ⟦ e2 ⟧ ⟦ c2 ⟧ i a a0). tauto.
    }
    rewrite H6.
    rewrite Sets_intersect_comm.
    rewrite Sets_full_intersect. reflexivity.
  }
  sets_unfold in H6.
  specialize (H6 s el1).
  destruct H6. clear H7. specialize (H6 H3).
  destruct H6.
  + pose proof (H5 s el1) as H_aux.
    assert ((x s el1 /\ noerrorLB ⟦ e2 ⟧ ⟦ c2 ⟧ s el1) /\ el1 = []).
      {
      split; [|tauto]. tauto.
      }
    specialize (H_aux H7).
    destruct H_aux. destruct H8. destruct H8.
    destruct H8. destruct H9. destruct H10.
    destruct H10.
    - left. split; [|tauto].
      unfold test_noio in H4.
      (*这边存在的情况是保证了没有io的x，没有io的条件通过test_noio传入证明内部*)
      exists (test_noio x ∩ noerrorLB ⟦ e2 ⟧ ⟦ c2 ⟧).
      sets_unfold.
      sets_unfold in H4.
      destruct H6.
      split.
      * unfold test_noio.
        intros.
        assert ((x a a0 /\ noerrorLB ⟦ e2 ⟧ ⟦ c2 ⟧ a a0) /\ a0 = []). {
          tauto.
        }
        specialize (H5 a a0 H13).
        destruct H5.
        destruct H5. destruct H5.
        destruct H5.
        destruct H14.
        exists x4. exists x5. exists x6.
        split; [tauto|]. split; [tauto|].
        destruct H15.
        ++ destruct H15. destruct H15. destruct H15. left.
          destruct H15. destruct H16. destruct H17.
          destruct H17.
          exists x7. exists x8. exists x9. tauto.
        ++ right. tauto.
      * unfold test_noio.
        tauto.
    - left. split;[|tauto].
      sets_unfold.
      exists (test_noio x ∩ noerrorLB ⟦ e2 ⟧ ⟦ c2 ⟧).
      sets_unfold.
      sets_unfold in H4.
      destruct H6.
      split.
      * unfold test_noio.
        intros.
        assert ((x a a0 /\ noerrorLB ⟦ e2 ⟧ ⟦ c2 ⟧ a a0) /\ a0 = []). {
          tauto.
        }
        specialize (H5 a a0 H13).
        destruct H5.
        destruct H5. destruct H5.
        destruct H5.
        destruct H14.
        exists x3. exists x4. exists x5.
        split; [tauto|]. split; [tauto|].
        destruct H15.
        ++ destruct H15. destruct H15. destruct H15. left.
          destruct H15. destruct H16. destruct H17.
          destruct H17.
          exists x6. exists x7. exists x8. tauto.
        ++ right. tauto.
       
      * unfold test_noio.
        tauto.
  + right.
    destruct H6.
    destruct H7.
    exists el1. exists el1.
    subst el1. simpl.
    split; [|tauto].
    split; [|tauto].
    exists x0. tauto.
Qed.

(*最后可以通过调用noio的函数，轻松证明noio的crefine特点，其他的部分的证明同bounded的部分类似*)
Lemma is_cinf_finiteio_aux:
  forall (e1 e2: expr) (c1 c2: com) n,
    e1 <<= e2 ->
    c1 <<= c2 ->
    crefine_cinf (is_cinf_finiteio ⟦ e1 ⟧ ⟦ c1 ⟧ n) (is_cinf_finiteio ⟦ e2 ⟧ ⟦ c2 ⟧ n) (⋃ (boundedLB_err ⟦ e2 ⟧ ⟦ c2 ⟧)).
Proof. 
  intros.
  unfold crefine_cinf.
  sets_unfold.
  (*对循环次数数学归纳*)
  induction n; simpl.
  + sets_unfold; tauto.
  + intros s1 el ?.
    pose proof test_true_mono e1 e2 H.
    pose proof H0.(cinf_crefine).
    unfold crefine_nrm in H2.
    unfold crefine_cinf in H3.
    destruct H1.
    - sets_unfold.
      destruct H1.
      * sets_unfold in H1.
        destruct H1 as (s2 & el1 & el2 & [? [? ?] ]).
        specialize (H2 s1 el1 s2 H4).
        destruct H2.
        ++ specialize (H3 s2 el2 H5).
           destruct H3.
           -- (*所有的都是没有出错的情况*)
              left; left; left. 
              exists s2, el1, el2; tauto.
           -- destruct H3 as (el3 & el4 & [? ?]). (*
          c2出错*)
              right.
              exists (el1 ++ el3), el4.
              split.
              ** exists (S O). simpl. sets_unfold. left.
                 exists s2, el1, el3. 
                split; [tauto|].
                split; [tauto|].
                right. tauto.
              ** rewrite <- H1. rewrite H6. rewrite app_assoc_reverse.
                tauto.
        ++ destruct H2 as (el3 & el4 & [? ?]). (*e2出错的情况*)
          right. exists el3. exists (el4 ++ el2).
          split.
          -- exists (S O). right. tauto.
          -- rewrite <- H1.
              rewrite H6.
              rewrite app_assoc_reverse. tauto.
      * sets_unfold in H1. (*后续noio的情况，直接调用前面证明的有关性质*)
        pose proof is_cinf_noio_ref e1 e2 c1 c2 H H0.
        unfold crefine_cinf in H4.
        specialize (H4 s1 el H1).
        unfold test_noio in H4.
        destruct H4.
        ++ sets_unfold in H4.
          destruct H4. destruct H4 as [tri ?]. destruct H4.
          left. left. right. 
          unfold test_noio.
          split; [|tauto].
          exists tri. tauto.
        ++ destruct H4 as [el1 ?]. destruct H4 as [el2 ?].
          destruct H4. destruct H4. 
          sets_unfold in H4.
          destruct H4 as [m ?].
          right. exists el1. exists el2.
          split; [|tauto].
          exists m. tauto.
    - sets_unfold in H1. (*递归向下的情况，需使用归纳条件*)
      destruct H1. destruct H1. destruct H1.
      destruct H1. destruct H4. 
      specialize (IHn x x1 H5).
      destruct H4. destruct H4. destruct H4. destruct H4.
      destruct H6. 
      sets_unfold.
      pose proof H0.(nrm_crefine) as H_nrm.
      unfold crefine_nrm in H_nrm.
      specialize (H_nrm x2 x4 x H7).
      specialize (H2 s1 x3 x2 H6).
      (*对归纳条件的出错情况进行讨论，证明和前面类似*)
      destruct IHn.
      * destruct H2.
        ++ destruct H_nrm.
           -- left. right.
              exists x. exists x0. exists x1.
              split; [tauto|].
              split; [|tauto].
              exists x2. exists x3. exists x4. tauto.
           -- destruct H9. destruct H9. destruct H9.
              right. exists (x3 ++ x5). exists (x6 ++ x1).
              split.
              ** exists (S n).
                 simpl. sets_unfold.
                 left. exists x2. exists x3. exists x5.
                 tauto.
              ** rewrite <- H1. rewrite <- H4. rewrite H10.
                rewrite ! app_assoc_reverse. tauto.
        ++ destruct H2. destruct H2. destruct H2.
           right.
           exists x5. exists (x6 ++ x4 ++ x1).
           split.
           -- exists (S n).
              simpl. sets_unfold.
              right. tauto.
           -- rewrite <- H1. rewrite <- H4. rewrite H9.
              rewrite ! app_assoc_reverse. tauto.
      * destruct H8. destruct H8. destruct H8. destruct H8.
        right.
        destruct H2.
        ++ destruct H_nrm.
          -- exists (x0 ++ x5). exists x6.
             split.
             ** exists (S x7).
                simpl. sets_unfold.
                left. exists x2. exists x3. exists (x4 ++ x5).
                split.
                *** rewrite <- H4. rewrite app_assoc_reverse. tauto.
                *** split; [tauto|]. left. 
                    exists x. exists x4. exists x5. tauto.
             ** rewrite <- H1. rewrite H9. rewrite app_assoc_reverse.
                tauto.
          -- destruct H10. destruct H10. destruct H10.
             exists (x3 ++ x8). exists (x9 ++ x1).
             split.
             ** exists (S x7).
                simpl. sets_unfold.
                left.
                exists x2. exists (x3). exists x8.
                split; [tauto|]. split; [tauto|].
                right. tauto.
             ** rewrite <- H1. rewrite <- H4.
                rewrite H11. rewrite ! app_assoc_reverse. tauto.
        ++ destruct H2. destruct H2. destruct H2.
           exists x8. exists (x9 ++ x4 ++ x1).
           split.
           ** exists (S x7). simpl. sets_unfold.
              right. tauto.
           ** rewrite <- H1. rewrite <- H4.
              rewrite H10. rewrite ! app_assoc_reverse. tauto.
Qed.

(*类比前面在event list的情况下的err的定义，本处对event stream的情况也需定义出错的可能性的集合，但由于err总是保持io有限，首先需要对其进行延拓。*)
Definition err_extend
           (D1_err: State -> event_list -> Prop): 
           State -> event_stream -> Prop :=
  fun s es =>
    exists el es1,
      D1_err s el /\ es = (StreamConn.stream_app el es1).

(*类似定义不出错的情况，本处是对event stream进行，故全集是任意形式的event stream，首先需要进行延拓才能取补集*)
Definition noerrorGeneral (D1: EDenote) (D2: CDenote): State -> event_stream -> Prop :=
  Sets.complement ((err_extend (⋃ (boundedLB_err D1 D2)))).

(*首先证明bounded_noio是符合精华关系的*)
Lemma bounded_noio_mono_aux:
  forall (e1 e2: expr) (c1 c2: com) n,
    e1 <<= e2 ->
    c1 <<= c2 ->
    crefine_nrm (bounded_noio ⟦ e1 ⟧ ⟦ c1 ⟧ n) (bounded_noio ⟦ e2 ⟧ ⟦ c2 ⟧ n) (boundedLB_err  ⟦ e2 ⟧ ⟦ c2 ⟧ n).
Proof.
  intros.
  unfold crefine_nrm.
  induction n; simpl.
  + sets_unfold; tauto.
  + sets_unfold; intros s1 el s2 ?.
    destruct H1.
    - destruct H1.
      left. left. tauto.
    - destruct H1. destruct H1. destruct H1. destruct H1. unfold silent in *.
      destruct H2.
      destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H5.
      pose proof H0.(nrm_crefine).
      unfold crefine_nrm in H7.
      specialize (H7 x2 x4 x H6).
      pose proof test_true_mono e1 e2 H.
      unfold crefine_nrm in H8.
      specialize (H8 s1 x3 x2 H5).
      destruct H8.
      * destruct H7.
        -- specialize (IHn  x x1 s2 H3).
          destruct IHn.
          ++ left. right. exists x. exists x0. exists x1.
            split; [tauto|].
            split.
            ** split; [|tauto].
              exists x2. exists x3. exists x4.
              tauto.
            ** tauto.
          ++ destruct H9. destruct H9. destruct H9.
            right. exists (x0 ++ x5). exists x6.
            split.
            ** left. exists x2. exists x3. exists (x4 ++ x5).
              split. rewrite <- H2. rewrite app_assoc_reverse. tauto.
              split; [tauto|].
              left. exists x. exists x4. exists x5.
              split; [tauto|]. tauto.
            ** rewrite <- H1. rewrite H10.
              rewrite app_assoc_reverse. tauto.
        -- destruct H7. destruct H7.
          destruct H7.
          right. exists (x3 ++ x5). exists (x6 ++ x1).
          split.
          ++ left. exists x2. exists x3. exists x5.
            split; [tauto|].
            split; [tauto|].
            right. tauto.
          ++ rewrite <- H1.
            rewrite <- H2.
            rewrite H9.
            rewrite ! app_assoc_reverse.
            tauto.
      * destruct H8. destruct H8. destruct H8.
        right.
        exists x5. exists (x6 ++ x4 ++ x1).
        split.
        -- right. tauto.
        -- rewrite <- H1.
          rewrite <- H2.
          rewrite H9.
          rewrite ! app_assoc_reverse. tauto.
Qed.

(*证明若是D1出现了error，那就不可能是noerror了*)
Lemma noerrorGeneral_fact1:
  forall (D1: EDenote) (D2: CDenote),
    err_extend (D1.(err)) ∩ noerrorGeneral D1 D2 == ∅.
Proof.
  intros.
  unfold noerrorGeneral, err_extend.
  sets_unfold.
  split.
  + intros. destruct H. destruct H0.
    destruct H. destruct H. destruct H.
    exists x. exists x0.
    split.
    - exists (S O).
      simpl. sets_unfold.
      right. tauto.
    - tauto.
  + tauto.   
Qed.

(*证明若是循环体出错，也不是noerror了*)
Lemma noerrorGeneral_fact2:
  forall (D1: EDenote) (D2: CDenote),
    err_extend (test_true D1 ∘ D2.(err)) ∩ noerrorGeneral D1 D2 == ∅.
Proof.
  intros.
  unfold noerrorGeneral, err_extend.
  sets_unfold.
  split.
  + intros. destruct H. destruct H0.
    destruct H. destruct H. destruct H.
    destruct H. destruct H. destruct H.
    destruct H. destruct H.
    exists (x2 ++ x3). exists x0.
    split.
    - destruct H1.
      exists (S O).
      simpl. sets_unfold.
      left.
      exists x1. exists x2. exists x3.
      tauto.
    - tauto.
  + tauto.
Qed.

(*一些关于自然数的辅助函数*)
Lemma plus_Sn_0 : forall (n': nat), n' = Nat.add n' 0 -> S n' = Nat.add (S n') 0.
Proof. 
  intros n' Hn'. 
  simpl. 
  rewrite <- Hn'. 
  reflexivity.
Qed.

Lemma n_add_0_n:
  forall (n: nat), n = Nat.add n 0.
Proof.
  intros.
  induction n. 
  - tauto.
  - pose proof plus_Sn_0 n IHn. tauto.
Qed.

Lemma n_add_s:
  forall (n1 n2: nat), 
    S (Nat.add n1 n2) = Nat.add n1 (S n2).
Proof.
  intros n1 n2.
  induction n1 as [| n1' IHn1].
  - simpl. reflexivity.
  - simpl. rewrite IHn1. reflexivity.
Qed.

(*辅助函数，证明若是在n轮内发生了错误，那么在n+1轮内也发生了错误*)
Lemma boundedLb_err_included:
  forall (D1: EDenote) (D2: CDenote) (n1 n2: nat),
  (boundedLB_err D1 D2 n1) ⊆ (boundedLB_err D1 D2 (Nat.add n1 n2)).
Proof.
  intros.
  induction n2.
  + sets_unfold.
    intros.
    induction n1.
    - tauto.
    - simpl. pose proof n_add_0_n n1. rewrite <- H0.
      simpl in H. tauto.
  + rewrite IHn2. 
    pose proof n_add_s n1 n2 as H_aux.
    rewrite <- H_aux. simpl.
    pose proof boundedLb_err_included_aux D1 D2 (n1 + n2).
    tauto.
Qed.

(*证明若是本身是没有error，那前面再加上一些noio的语句执行，同样是没有error的*)
Lemma noerrorGeneral_aux:
  forall (D1: EDenote) (D2: CDenote) (s1 s2: State) (es1 es2: event_stream) (el: event_list) (n: nat),
    ((bounded_noio D1 D2 n) s1 el s2) -> es1 = StreamConn.stream_app el es2 -> noerrorGeneral D1 D2 s1 es1 ->
    noerrorGeneral D1 D2 s2 es2.
Proof.
  intros D1 D2 s1 s2 es1 es2 el n H H0.
  unfold noerrorGeneral.
  (*转化成证明逆否命题*)
  pose proof contrapositive (Sets.complement (err_extend (⋃ (boundedLB_err D1 D2))) s2 es2) (Sets.complement (err_extend (⋃ (boundedLB_err D1 D2))) s1 es1).
  apply H1.
  sets_unfold.
  intros.
  apply double_neg_elim.
  apply double_neg_elim1 in H2.
  unfold err_extend in H2.
  unfold err_extend.
  destruct H2. destruct H2.
  destruct H2.
  destruct H2.
  exists (el ++ x). exists x0.
  split.
  + exists (Nat.add n x1).
    clear H1.
    revert s1 s2 es1 es2 H0 H H2 H3.
    induction n, x1.
    - simpl. tauto.
    - simpl. intros. simpl in H. tauto.
    - simpl. intros. simpl in H2. tauto.
    - simpl. intros. 
      destruct H.
      * sets_unfold in H. destruct H.
        subst s1. rewrite H. simpl.
        pose proof boundedLb_err_included D1 D2 (S x1) n.
        sets_unfold in H1.
        specialize (H1 s2 x H2).
        pose proof boundedLb_err_included_aux D1 D2 (S x1 + n).
        sets_unfold in H4.
        specialize (H4 s2 x H1).
        simpl in H4.
        pose proof n_add_s n x1.
        rewrite <- H5. simpl. 
        rewrite Nat.add_comm.
        tauto.
      * unfold silent in H.
        sets_unfold in H.
        destruct H. destruct H. destruct H.
        destruct H. destruct H1.
        destruct H1. rewrite H5 in H. simpl in H.
        subst x4.
        specialize (IHn x2 s2 es1 es2 H0 H4 H2 H3).
        sets_unfold.
        destruct H1. destruct H. destruct H.
        destruct H. destruct H1.
        subst x3.
        left. 
        exists x4. exists x5. exists (x6 ++ el ++ x).
        split.
        ** rewrite app_assoc. rewrite H5. simpl. tauto.
        ** split. tauto.
          left. exists x2. exists x6. exists (el ++ x).
          tauto.
  + rewrite H0. rewrite H3.
    symmetry.
    apply StreamConn.stream_ACC_Assoc.
Qed.     

(*证明了一种出错的情况，即noio的语句只有D1出错*)
Lemma no_io_err (D1: EDenote) (D2: CDenote):
  forall (s1 s2: State) (el1 el2: event_list) (n: nat),
    bounded_noio D1 D2 n s1 el1 s2 ->
    D1.(err) s2 el2 ->
    boundedLB_err D1 D2 (S n) s1 (el1 ++ el2).
Proof.
  intros.
  revert s1 s2 el1 el2 H H0.
  induction n.
  + intros. tauto.
  + intros. simpl in *.
    destruct H.
    - sets_unfold in H. destruct H.
      subst s1. subst el1. simpl. right. tauto.
    - unfold silent in H.
      sets_unfold in H.
      destruct H. destruct H. destruct H.
      destruct H. destruct H1. destruct H1. destruct H1.
      destruct H1. destruct H1.
      destruct H1. destruct H4.
      specialize (IHn x s2 x1 el2 H2 H0).
      sets_unfold in IHn.
      sets_unfold. left. exists x2. exists x3. exists (x4 ++ x1 ++ el2).
      split. rewrite app_assoc. rewrite H1. rewrite app_assoc. rewrite H. tauto. split. tauto. left.
      exists x. exists x4. exists (x1 ++ el2). tauto.
Qed.

(*第二种出错的情况，即noio的语句只有循环体本身出错*)
Lemma no_io_err2 (D1: EDenote) (D2: CDenote):
  forall (s1 s2 s3: State) (el1 el2 el3: event_list) (n: nat),
    bounded_noio D1 D2 n s1 el1 s2 ->
    test_true D1 s2 el2 s3 ->
    D2.(err) s3 el3 ->
    boundedLB_err D1 D2 (S n) s1 (el1 ++ el2 ++ el3).
Proof.
  intros.
  revert s1 s2 s3 el1 el2 el3 H H0 H1.
  induction n.
  + intros. tauto.
  + intros. simpl in *.
    destruct H.
    - sets_unfold in H. destruct H. left.
      sets_unfold.
      exists s3. exists (el1 ++ el2). exists el3.
      split.
      * apply app_assoc_reverse.
      * rewrite H. simpl. rewrite H2. split; [tauto|].
        right. tauto.
    - unfold silent in H.
      sets_unfold in H.
      destruct H. destruct H. destruct H.
      destruct H. destruct H2. destruct H2.
      destruct H2. destruct H2. destruct H2.
      destruct H2. destruct H5.
      specialize (IHn x s2 s3 x1 el2 el3 H3 H0 H1).
      sets_unfold. left.
      exists x2. exists x3. exists (x4 ++ x1 ++ el2 ++ el3).
      split.
      * rewrite <- H.
        rewrite <- H2.
        rewrite ! app_assoc_reverse.
        tauto.
      * split; [tauto|]. left.
        exists x. exists x4. exists (x1 ++ el2 ++ el3).
        split; [tauto|].
        split; [tauto|tauto].
Qed.

(*若符合is_ioinf e1 c1，那么去除掉可能在e2 c2中出错的可能性，剩下的一定是满足is_ioinf e2 c2*)
Lemma ioinf_mono_aux:
  forall (e1 e2: expr) (c1 c2: com) X,
    e1 <<= e2 ->
    c1 <<= c2 ->
    is_ioinf ⟦ e1 ⟧ ⟦ c1 ⟧ X -> 
    is_ioinf ⟦ e2 ⟧ ⟦ c2 ⟧ (X ∩ noerrorGeneral ⟦ e2 ⟧ ⟦ c2 ⟧). 
Proof.
  unfold is_ioinf.
  sets_unfold.
  intros.
  destruct H2.
  specialize (H1 a a0 H2).
  pose proof bounded_noio_mono_aux e1 e2 c1 c2.
  destruct H1.
  - left. destruct H1. destruct H1. destruct H1.
    exists x. exists x0. exists x1.
    destruct H1. destruct H5.
    split; [tauto|].
    unfold crefine_nrm in H4.
    destruct H5.
    specialize (H4 x2 H H0 a x0 x H5).
    (*证明在noerror的前提下，另外一种boundedLB_err的情况实际上是不可能的*)
    assert (bounded_noio ⟦ e2 ⟧ ⟦ c2 ⟧ x2 a x0 x). {
      unfold noerrorGeneral in H3.
      destruct H4. tauto. 
      destruct H3.
      unfold err_extend.
      destruct H4. destruct H3.
      exists x3. exists (StreamConn.stream_app x4 x1).
      destruct H3.
      split.
      * exists x2. tauto.
      * rewrite <- H1.
        rewrite H4. 
        apply StreamConn.stream_ACC_Assoc.
    }
    split.
    * exists x2. tauto.
    * destruct H6. destruct H6. destruct H6.
      exists x3. exists x4. exists x5.
      pose proof test_true_mono _ _ H.
      unfold crefine_nrm in H8.
      destruct H6. destruct H9.
      specialize (H8 x x4 x3 H9).
      destruct H8.
      ** split; [tauto|]. split; [tauto|]. 
        (*证明在noerror的前提下不可能进入err的分支*)
        pose proof H0.(ioinf_crefine).
        unfold crefine_ioinf in H11.
        specialize (H11 x3 x5 H10).
        destruct H11; [tauto|].
        destruct H11. destruct H11.
        pose proof noerrorGeneral_fact2 ⟦ e2 ⟧ ⟦ c2 ⟧.
        sets_unfold in H12.
        specialize (H12 x x1).
        destruct H12. destruct H12.
        unfold err_extend.
        split.
        destruct H11.
        ++ exists (x4 ++ x6). exists x7. 
          split. exists x3. exists x4. exists x6. tauto.
          rewrite <- H6. rewrite H12.
          symmetry.
          apply StreamConn.stream_ACC_Assoc.
        ++ symmetry in H1.
          pose proof noerrorGeneral_aux ⟦ e2 ⟧ ⟦ c2 ⟧ a x a0 x1 x0 x2 H7 H1 H3.
          tauto.
      ** symmetry in H1.
        (*也是证明不可能落入err的分支，本处是表达式出现错误*)
        pose proof noerrorGeneral_aux ⟦ e2 ⟧ ⟦ c2 ⟧ a x a0 x1 x0 x2 H7 H1 H3 as H_aux. 
        unfold noerrorGeneral in H3. sets_unfold in H3.
        destruct H3. destruct H8. destruct H3.
        unfold err_extend.
        exists (x0 ++ x6). exists (StreamConn.stream_app x7 x5).
        split.
        -- pose proof noerrorGeneral_fact2 ⟦ e2 ⟧ ⟦ c2 ⟧.
          sets_unfold in H8.
          specialize (H8 x x1).
          destruct H8. destruct H8.
          unfold err_extend.
          split.
          ++ pose proof noerrorGeneral_fact1 ⟦ e2 ⟧ ⟦ c2 ⟧.
            sets_unfold in H8. specialize (H8 x x1).
            destruct H8. destruct H8.
            split.
            unfold err_extend.
            exists x6. exists (StreamConn.stream_app x7 x5).
            split. tauto.
            destruct H3.
            rewrite <- H6. rewrite H8. 
            apply StreamConn.stream_ACC_Assoc.
            tauto.
          ++ tauto.
        -- rewrite H1.
          rewrite <- H6.
          destruct H3.
          rewrite H8.
          transitivity (StreamConn.stream_app x0 (StreamConn.stream_app x6 (StreamConn.stream_app x7 x5))).
          ++ symmetry.
            assert (StreamConn.stream_app x6 (StreamConn.stream_app x7 x5) = StreamConn.stream_app (x6 ++ x7) x5). { symmetry. apply StreamConn.stream_ACC_Assoc. }
            rewrite H11. reflexivity.
          ++ symmetry. apply StreamConn.stream_ACC_Assoc.
  - right.
    destruct H1. destruct H1. destruct H1.
    destruct H1.
    destruct H5.
    pose proof test_true_mono e1 e2 H.
    destruct H5. destruct H5. destruct H5.
    destruct H5. destruct H5. destruct H8. destruct H8.
    destruct H8. destruct H8. destruct H8. destruct H8. destruct H10.
    destruct H5 as [n ?].
    specialize (H7 x2 x5 x0 H10).
    specialize (H4 n H H0).
    unfold crefine_nrm in H4.
    specialize (H4 a x3 x2 H5).
    (*不可能落入出错的可能，和上面的证明略有不同*)
    assert (bounded_noio ⟦ e2 ⟧ ⟦ c2 ⟧ n a x3 x2) as H_bounded. {
      unfold noerrorGeneral in H3.
      destruct H4. tauto. 
      destruct H3.
      unfold err_extend.
      destruct H4. destruct H3. destruct H3.
      exists x7. exists (StreamConn.stream_app (x8 ++x4) x1).
      split.
      *** exists n. tauto.
      *** rewrite <- H1.
          rewrite H4.
          rewrite app_assoc_reverse.
          apply StreamConn.stream_ACC_Assoc.
    }
    assert (a0 = StreamConn.stream_app x3 (StreamConn.stream_app x4 x1)) as H_. {
      rewrite <- H1.
      apply StreamConn.stream_ACC_Assoc.
    }
    pose proof noerrorGeneral_aux ⟦ e2 ⟧ ⟦ c2 ⟧ a x2 a0 (StreamConn.stream_app x4 x1) x3 n H_bounded H_ H3 as H_aux.
    exists x. exists (x3 ++ x4). exists (x1).
    split; [tauto|].
    split. 
    * destruct H7.
      -- pose proof H0.(nrm_crefine).
          unfold crefine_nrm in H12.
          specialize (H12 x0 x6 x H11).
          (*不会落入c2出错的分支*)
          assert (⟦ c2 ⟧.(nrm) x0 x6 x). {
            unfold noerrorGeneral in H3.
            destruct H12. tauto. 
            destruct H3.
            unfold err_extend.
            destruct H12. destruct H3. destruct H3.
            exists (x3 ++ x5 ++ x7). exists (StreamConn.stream_app x8 x1).
            split.
            *** sets_unfold.
              exists (S n).
              simpl.
              sets_unfold.
              pose proof noerrorGeneral_fact2 ⟦ e2 ⟧ ⟦ c2 ⟧.
              sets_unfold in H13.
              specialize (H13 x2 (StreamConn.stream_app x4 x1)).
              destruct H13. destruct H13.
              unfold err_extend.
              split.
              -- exists (x5 ++ x7). exists (StreamConn.stream_app x8 x1). 
                  split.
                  ++ exists x0. exists x5. exists x7. tauto.
                  ++ rewrite <- H8. rewrite H12.
                    rewrite app_assoc.
                    apply StreamConn.stream_ACC_Assoc.
              --  tauto.
            *** rewrite <- H1.
                rewrite <- H8.
                rewrite H12.
                assert ((x3 ++ x5 ++ x7) ++ x8 = x3 ++ x5 ++ x7 ++ x8). {
                  rewrite app_assoc_reverse.
                  rewrite app_assoc_reverse.
                  tauto.
              }
              rewrite <- H13.
              apply StreamConn.stream_ACC_Assoc.
          }
          exists x2. exists x3. exists x4.
          split. tauto. split. exists n. tauto.
          split. exists x0. exists x5. exists x6. tauto. tauto.
      -- pose proof noerrorGeneral_fact1 ⟦ e2 ⟧ ⟦ c2 ⟧. (*noerror的情况下e2出错是不可能的*)
        sets_unfold in H12. 
        specialize (H12 x2 (StreamConn.stream_app x4 x1)).
        destruct H12. destruct H12.
        destruct H7. destruct H7. destruct H7.
        split.
        ++ unfold err_extend.
          exists x7. exists (StreamConn.stream_app (x8 ++ x6) x1).
          split. tauto.
          rewrite <- H8. rewrite H12.
          rewrite app_assoc_reverse.
          apply StreamConn.stream_ACC_Assoc.
        ++ tauto. 
    * split; [tauto|].
      (*已知noerror和第一轮执行没有出错，那么从第二轮开始向后的肯定也是noerror*)
      revert H_aux.
      (*逆否命题更好证明，所以先转化为逆否命题，证明的是noerror的情况*)
      apply contrapositive.
      unfold noerrorGeneral.
      sets_unfold.
      intros.
      apply double_neg_elim.
      apply double_neg_elim1 in H12.
      unfold err_extend in *.
      destruct H12. destruct H12. destruct H12.
      destruct H12.
      clear H7. clear H4. exists (x4 ++ x7).
      exists x8.
      split.
      *** exists (S x9).
        simpl. left.
        sets_unfold.
        exists x0. exists x5. exists (x6 ++ x7).
        split.
        -- rewrite app_assoc. rewrite H8. tauto.
        -- pose proof test_true_mono e1 e2 H. 
            unfold crefine_nrm in H4.
            specialize (H4 x2 x5 x0 H10).
            assert (test_true ⟦ e2 ⟧ x2 x5 x0). {
              destruct H4. tauto.
              unfold noerrorGeneral in H3. sets_unfold in H3. destruct H3.
              unfold err_extend.
              destruct H4. destruct H3. destruct H3.
              exists (x3 ++ x10). exists (StreamConn.stream_app (x11 ++ x6) x1).
              split.
              + exists (S n).
                simpl.
                pose proof no_io_err ⟦ e2 ⟧ ⟦ c2 ⟧ a x2 x3 x10 n H_bounded H3.
                tauto.
              + rewrite H_.
                rewrite <- H8.
                rewrite H4. 
                rewrite app_assoc_reverse.
                assert (StreamConn.stream_app (x10) (StreamConn.stream_app (x11 ++ x6) x1) = (StreamConn.stream_app (x10 ++ x11 ++ x6) x1)). {
                  symmetry.
                  apply StreamConn.stream_ACC_Assoc.
                }
                rewrite <- H7. symmetry.
                apply StreamConn.stream_ACC_Assoc.
            }
            split.
          ++ tauto. 
          ++ left.
            pose proof H0.(nrm_crefine).
            unfold crefine_nrm in H14.
            specialize (H14 x0 x6 x H11).
            assert (⟦ c2 ⟧.(nrm) x0 x6 x). {
              destruct H14. tauto.
              destruct H14. destruct H14.
              destruct H14.
              unfold noerrorGeneral in H3. sets_unfold in H3.
              destruct H3.
              unfold err_extend.
              exists (x3 ++ x5 ++ x10).
              exists (StreamConn.stream_app x11 x1).
              split.
              + exists (S n).
                simpl.
                pose proof no_io_err2 ⟦ e2 ⟧ ⟦ c2 ⟧ a x2 x0 x3 x5 x10 n H_bounded H7 H14.
                tauto.
              + rewrite H_.
                rewrite <- H8.
                rewrite H15.
                assert (
                  StreamConn.stream_app (x5 ++ x10)
                    (StreamConn.stream_app x11 x1) =
                    (StreamConn.stream_app (x5 ++ x10 ++ x11) x1)). {
                      symmetry.
                      rewrite app_assoc.
                      apply StreamConn.stream_ACC_Assoc.
                    }
                assert (StreamConn.stream_app x3 (StreamConn.stream_app (x5 ++ x10)
                (StreamConn.stream_app x11 x1)) = StreamConn.stream_app x3 
                (StreamConn.stream_app (x5 ++ x10 ++ x11) x1)). {
                  symmetry.
                  rewrite H3. tauto. 
                }
                rewrite <- H16.
                symmetry.
                apply StreamConn.stream_ACC_Assoc.
            }
            exists x. exists x6. exists x7.
            split; [tauto|]. tauto.
      *** rewrite H13. symmetry.
        apply StreamConn.stream_ACC_Assoc.
Qed. 

Instance CWhile_mono:
  Proper (erefine ==> crefine ==> crefine) CWhile.
Proof.
  unfold Proper, respectful.
  intros e1 e2 ? c1 c2 ?.
  split; simpl.
  + unfold crefine_nrm.
    sets_unfold.
    intros.
    destruct H1.
    pose proof boundedLB_nrm_mono_aux e1 e2 c1 c2 x H H0.
    unfold crefine_nrm in H2.
    specialize (H2 s1 el1 s2).
    pose proof H2 H1.
    destruct H3.
    - left.
      exists x.
      tauto.
    - right.
      destruct H3. destruct H3.
      exists x0. exists x1. 
      split.
      * exists x.
        tauto.
      * tauto.
  + unfold crefine_err.
    sets_unfold.
    intros.
    destruct H1.
    pose proof boundedLB_err_mono_aux e1 e2 c1 c2 x H H0.
    unfold crefine_err in H2.
    specialize (H2 s el1).
    pose proof H2 H1.
    destruct H3.
    destruct H3.
    exists x0.
    exists x1.
    split.
    * exists x.
      tauto.
    * tauto.
  + unfold crefine_cinf.
    sets_unfold. intros.
    destruct H1.
    pose proof is_cinf_finiteio_aux e1 e2 c1 c2 x H H0.
    unfold crefine_cinf in H2.
    specialize (H2 s el1 H1).
    destruct H2.
    - left.
      exists x. tauto.
    - right.
      destruct H2. destruct H2.
      exists x0. exists x1.
      split.
      * destruct H2. sets_unfold in  H2. destruct H2.
       exists x2. tauto.
      * tauto.
  + unfold crefine_ioinf.
    intros. sets_unfold in H1. destruct H1. destruct H1.
    pose proof ioinf_mono_aux e1 e2 c1 c2 x H H0 H1. (*X交上不在e2，c2出错的情况，那么就是ioinf的*)
    sets_unfold.
    assert ((exists x0, (x0 ⊆ (noerrorGeneral ⟦ e2 ⟧ ⟦ c2 ⟧)) /\ (is_ioinf ⟦ e2 ⟧ ⟦ c2 ⟧ x0) /\ x0 s es1) -> ((Sets.general_union (is_ioinf ⟦ e2 ⟧ ⟦ c2 ⟧) s es1))). {
      intros.
      sets_unfold.
      destruct H4. destruct H4.
      exists x0.
      tauto.
    }
    unfold is_ioinf.
    unfold is_ioinf in H3.
    sets_unfold in H3.
    (*分类讨论出错和没有出错两种情况*)
    assert (forall (s: State) (es: event_stream), x s es-> x s es /\ noerrorGeneral ⟦ e2 ⟧ ⟦ c2 ⟧ s es \/ x s es /\ (err_extend (⋃ (boundedLB_err ⟦ e2 ⟧ ⟦ c2 ⟧)))s es) as H_. {
      unfold noerrorGeneral, err_extend.
      sets_unfold.
      intros.
      tauto.
    }
    sets_unfold.
    pose proof (H_ s es1 H2).
    destruct H5.
    - left.
      apply H4.
      exists (x ∩ noerrorGeneral ⟦ e2 ⟧ ⟦ c2 ⟧).
      split.
      * sets_unfold.
        intros. tauto.
      * unfold is_ioinf.
        sets_unfold.
        tauto.
    - right.      
      destruct H5.
      unfold err_extend in H6.
      tauto.
Qed.



