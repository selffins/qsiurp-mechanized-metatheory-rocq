(** Modules tutorial from https://rocq-prover.github.io/platform-docs/RequireImportTutorial.html
    Copied almost verbatim.
 *)

(**  List of commands
     1. [Print _]
     2. [Check _]
     3. [From _ Require _]
     4. [Search _]
     5. [Locate _]
     6. [Import _]
     7. [About _]
 *)

(** 1. Library files, modules, and identifiers *)
(** 1.1. The Require command and fully qualified names *)

(**  Coq's initial state is populated by a dozen library files called the [Prelude] *)
Print Libraries.
Check or_comm.
From Stdlib Require Bool.Bool.

(** The previous command loaded the file Bool.vo in Coq's stdlib. *)
Print Libraries.

(** [Require file] recursively [Require]s any file it has [Require]d *)
(** There is no way to unrequire a library.  *)

Search andb true.
About andb_prop.
About Bool.andb_true_l.

(**  [Coq.Bool.Bool.and_true_l] is the internal, canonical name of [and_true_l] - called a fully qualified identifier. *)
Locate andb_true_l.
Import Bool.
Check andb_true_l.
Search andb true.

(**  Usually: From Stdlib.Bool Require Import Bool *)
(**  Form is a convenience to require multiple parts from a commmon sublibrary *)
(**  e.g. From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq. *)

(**  1.2 Basic modules and the [Import] command *)
Module Foo.
  Definition foo := 42.
  Lemma bar : 21 * 2 = foo.
  Proof. reflexivity. Qed.
  Lemma baz : 21 + 21 = foo.
  Proof. auto. Qed.
End Foo.

(** Interesting: The two lemmas are printed as [Parameter]s. And the module is a [Struct]. *)
Print Module Foo.

(** Dot syntax *)
Print Foo.foo.
Check Foo.bar.
Print Foo.bar.
Check Foo.baz.
Print Foo.baz.

(** "Closed under the global context" means they are proved (not relying on an axiom) *)
Print Assumptions Foo.bar.
Print Assumptions Foo.baz.

Fail Check baz.
Fail Check bar.

(** We can use Foo and prove lemmas about it via dot syntax *)
Lemma forty : Foo.foo - 2 = 40.
Proof.
  unfold Foo.foo.
  fold Foo.foo.
  rewrite <- Foo.bar.
  reflexivity.
Qed.

(** Library files are modules, which is why they both use dot syntax. *)
Print Module Stdlib.Bool.Bool.
Import Foo.
Check bar.

(** In short, we [Require] library files to load their content, and [Import] modules to use short names for their content. *)

(** 1.3. Name clashes and disambiguation *)

(** Creating another module with the same [foo]... *)
Module OtherFoo.
  Definition foo := true.
End OtherFoo.

Import OtherFoo.
Print foo.
About foo.

(** [OtherFoo.foo] has shadowed [Foo.foo]. We now need to use a more qualified name for [foo]. *)
Print foo.
About foo.
Locate foo.

(** [Locate] gives us two locations for [foo]. *)
Locate Foo.foo.

(** [Import]ing again simply shadows [OtherFoo.foo]. *)
Import Foo.
Print foo.
About foo.
Locate foo.

(** Therefore, the order of [Import] commands matter.
    You can use more qualified names to avoid this shadowing business, however. *)

(** For a more "real" example, consider [Stdlib]'s two different number libraries. *)
From Stdlib Require Import Arith.PeanoNat ZArith.BinInt.

Check Nat.add_0_r.
Check Z.add_0_r.

Fail Check add_0_r.
Locate add_0_r.

(** Output:
[Constant Stdlib.Arith.PeanoNat.Nat.add_0_r (shorter name to refer to it in current context is Nat.add_0_r)] *)

Import Nat.
Check add_0_r.
About add_0_r.

Import Z.
Check add_0_r.
About add_0_r.

About Nat.
About Corelib.Init.Nat.

(** Nested modules (two nested modules sharing the same name, e.g. [ABC] ). *)
Module NestedABC1.
  Module ABC.
    Definition alice := 1.
    Definition bob := 1.
  End ABC.
End NestedABC1.

Module NestedABC2.
  Module ABC.
    Definition alice := 2.
    Definition charlie := 2.
  End ABC.
End NestedABC2.

Locate alice.
Locate bob.
Locate charlie.

Import NestedABC1.
Print ABC.alice.
Print ABC.bob.
Import NestedABC2.
Print ABC.alice.
Print ABC.bob.

(** In short,
   1. it is possible to have two files with the same name as long as they are in different directories,
   2. it is possible to have two non-file modules with the same name as long as they are in different modules,
   3. it is possible to have two constants with the same name as long as they are in different modules.
 *)

(** 1.4 Other content types in Modules *)

(** There can be many content types in a module, including:
    1. parameters and axioms
    2. tactics
    3. notations, abbreviations, [Ltac] and [Ltac2] notations
    4. hints and type class instances
    5. coercions
    6. canonical structures
 *)

Module Bar.
  (* A parameter: *)
  Parameter (secret : nat).
  (* An axiom: *)
  Axiom secret_is_42 : secret = 42.
  (* A custom tactic: *)
  Ltac find_secret := rewrite secret_is_42.
  (* An abbreviation: *)
  Notation add_42 := (Nat.add 42).
  (* A tactic notation: *)
  Tactic Notation "fs" := find_secret.
  (* A notation: *)
  Infix "+p" := Nat.add (only parsing, at level 30, right associativity) : nat_scope.
  (* Two lemmas: *)
  Lemma secret_42 : secret = 42.
  Proof. find_secret. reflexivity. Qed.
  Lemma baz : 21 +p 21 = secret.
  Proof. fs. reflexivity. Qed.
End Bar.

About Bar.secret.
 About Bar.secret_is_42.
Print Assumptions Bar.secret_is_42.
About Bar.secret_42.
Print Assumptions Bar.secret_42.
About Bar.baz.
Print Assumptions Bar.baz.

(* To be continued... *)
