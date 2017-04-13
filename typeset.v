Require Import Arith.
Require Import List.

Inductive SharedVar := Sh : nat -> SharedVar.
Inductive LocalVar := Lc : nat -> LocalVar.

Definition beq_ShVar :=
fun a b => match a with
         | Sh a' => match b with
                   | Sh b' => beq_nat a' b' 
                   end
         end.

Definition beq_LcVar :=
  fun a b => match a with
           | Lc a' => match b with
                     | Lc b' => beq_nat a' b'
                     end
           end.

Inductive Variabl :=
  | SVar : SharedVar -> Variabl
  | LVar : LocalVar -> Variabl.

Definition beq_Var :=
  fun a b => match a with
           | SVar a' => match b with
                       | SVar b' =>  beq_ShVar a' b'
                       | _ => false
                       end
           | LVar a' => match b with
                       | LVar b' => beq_LcVar a' b'
                       | _ => false
                       end
           end.

Definition Const : Set := nat.

Inductive Expr :=
| E_SVar : SharedVar -> Expr
| E_LVar : LocalVar -> Expr
| E_Const : Const -> Expr
| E_Plus : Expr -> Expr -> Expr
| E_Load : SharedVar -> Expr.

Inductive BExpr : Type :=
| B_True : BExpr
| B_False : BExpr
| B_Eq : Expr -> Expr -> BExpr.

Inductive Stmt : Type :=
| S_Skip : Stmt
| S_Seq : Stmt -> Stmt -> Stmt
| S_Ass_Loc : LocalVar -> Expr -> Stmt
| S_Ass_Sh : SharedVar -> Expr  -> Stmt
| S_Store : SharedVar -> Expr -> Stmt
| S_If : BExpr -> Stmt -> Stmt -> Stmt.


Definition Prog : Type := (nat -> Stmt) * nat.

Inductive is_redex_stmt : Stmt -> Prop :=
| TWO_SKIP : is_redex_stmt (S_Seq S_Skip S_Skip)
| LOCAL_ASS : forall (r:LocalVar) (n:nat),is_redex_stmt (S_Ass_Loc r (E_Const n))
| SHARED_ASS : forall (X:SharedVar) (n:nat), is_redex_stmt (S_Ass_Sh X (E_Const n))
| STORE : forall (X:SharedVar) (n:nat), is_redex_stmt (S_Store X (E_Const n))
| IF_TRUE : forall (c1 c2:Stmt), is_redex_stmt (S_If B_True c1 c2)
| IF_FALSE : forall (c1 c2:Stmt), is_redex_stmt (S_If B_False c1 c2).

Inductive is_redex_expr : Expr -> Prop :=
| SHARED : forall (X:SharedVar), is_redex_expr (E_SVar X)
| LOCAL : forall (r:LocalVar), is_redex_expr (E_LVar r)
| PLUS : forall (n1 n2:nat), is_redex_expr (E_Plus (E_Const n1) (E_Const n2))
| LOAD : forall (X:SharedVar), is_redex_expr (E_Load X).

Inductive is_redex_bexpr : BExpr -> Prop :=
| EQ : forall (n1 n2:nat), is_redex_bexpr (B_Eq (E_Const n1) (E_Const n2)).


Inductive Value :=
| V_Int : nat -> Value
| V_Bool : bool -> Value.

Definition State := Variabl -> Value.
Inductive Label :=
| L_normal : Label
| L_sc : Label
| L_na : Label.
Definition rs := list Variabl.
Definition ws := list Variabl.
Definition tid := nat.

Definition X := Sh 0.
Definition Y := Sh 1.
Definition Z := Sh 2.
Definition r := Lc 0.
Definition s := Lc 1.
Definition t := Lc 2.

Definition s1 := S_If (B_Eq (E_Const 1) (E_Const 2)) S_Skip S_Skip.
Definition state0 (v:Variabl) := V_Int 0.

Definition update (st:State) (var:Variabl) (val:Value) : State :=
  fun (v:Variabl) => if beq_Var v var then val else st v.

Definition state1 := (update state0 (SVar X) (V_Int 1)).
Eval vm_compute in (state1 (SVar Z)).

Inductive Small_step_stmt : Stmt * State  -> Label -> rs * ws -> Stmt * State -> Prop :=
| RS_Seq_Skip : forall st:State, Small_step_stmt ((S_Seq S_Skip S_Skip),st) L_normal (nil,nil) (S_Skip,st)
| RS_Ass_Loc : forall (st:State) (n:nat) (r:LocalVar), Small_step_stmt ((S_Ass_Loc r (E_Const n)),st) L_normal (nil,(LVar r)::nil) (S_Skip, update st (LVar r) (V_Int n))
| RS_Ass_Sh : forall (st:State) (n:nat) (X:SharedVar), Small_step_stmt ((S_Ass_Sh X (E_Const n)),st) L_na (nil,(SVar X)::nil) (S_Skip, update st (SVar X) (V_Int n))
| RS_Ass_Store : forall (st:State) (n:nat) (X:SharedVar), Small_step_stmt ((S_Store X (E_Const n)),st) L_sc (nil,(SVar X)::nil) (S_Skip, update st (SVar X) (V_Int n))
| RS_If_True : forall (st: State) (c1 c2:Stmt), Small_step_stmt ((S_If (B_True) c1 c2),st) L_normal (nil,nil) (c1,st)
| RS_If_False : forall (st: State) (c1 c2:Stmt), Small_step_stmt ((S_If (B_False) c1 c2),st) L_normal (nil,nil) (c2,st).

Inductive Small_step_expr : Expr*State -> Label -> rs*ws -> Expr * State ->Prop :=
| RE_X : forall (st:State) (X:SharedVar) (n:nat), st (SVar X) = (V_Int n) -> Small_step_expr (E_SVar X,st) L_na ((SVar X)::nil,nil) ((E_Const n, st))
| RE_r : forall (st:State) (r:LocalVar) (n:nat), st (LVar r) = (V_Int n) -> Small_step_expr (E_LVar r,st) L_na ((LVar r)::nil,nil) ((E_Const n, st))
| RE_n1n2 : forall (st:State) (n1 n2 n:nat), n1+n2 = n -> Small_step_expr (E_Plus (E_Const n1) (E_Const n2), st) L_normal (nil,nil) (E_Const n, st)
| RE_load : forall (st:State) (X:SharedVar) (n:nat), st (SVar X) = (V_Int n) -> Small_step_expr (E_load X,st) L_sc ((SVar X)::nil,nil) ((E_Const n, st)).


Inductive Small_step_bexpr : BExpr*State -> Label -> rs*ws -> BExpr * State ->Prop :=
| RB_Eq : forall (st:State) (n1 n2 :nat), n1=n2 -> Small_step_bexpr (B_Eq (E_Const n1) (E_Const n2), st) L_normal (nil,nil) (B_True,st)
| RB_Neq : forall (st:State) (n1 n2 :nat), ~(n1=n2) -> Small_step_bexpr (B_Eq (E_Const n1) (E_Const n2), st) L_normal (nil,nil) (B_False,st).

Inductive Small_step_porg : Prog *State -> tid -> Label -> rs*ws -> Prog *State ->Prop:=
| RP_Choose : forall (st st':State) (f:nat->Stmt) (m:nat) (i:nat) (c':Stmt) omega delta, Small_step_stmt (f i,st) omega delta (c',st') -> Small_step_porg ((f,m),st) i omega delta (((fun j => if beq_nat i j then c' else f i),m), st')
| RP_Terminate : forall (st:State) (m:nat), Small_step_porg ((fun _ => S_Skip, m), st) 0 L_normal (nil,nil) ((fun _ => S_Skip,1),st).

