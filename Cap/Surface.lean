/-
A surface front end for the deep command language.

`#own_prog o D { ... }` elaborates a small command syntax to a `List Cap.Cmd`
and runs the executable checker `Cap.check` *at elaboration time*: an accepted
program is logged and a refused one is a compile error carrying the checker's
message. `#own_prog` is a checking front end: it declares nothing. `#own_cert` is the
proof-producing form: it translates the same surface commands to the deep list and
declares `theorem n : Checked o D [..] := by unfold Checked; decide`, so the kernel
checks a certificate for the closed program. Neither is the hidden-index elaborator
of the design;
there are no index refinements, no `Checked` hypotheses and no `Cmd`-level
soundness facts derived here.

The command terms are the deep language's arguments: capability identifiers have
type `CapId`, indices and shares type `Nat`. `splitFraction` takes its two shares
as numerals and derives the required positivity proofs with `by decide`; a share
that does not reduce (a variable, say) is refused at elaboration. Because the
whole program is checked while the command is elaborated, the owner must reduce
to a closed value: a program whose owner is abstract cannot be run and is
rejected rather than assumed.

A positive program appears below; the negative control lives in
`bench/CapSurfaceReject.lean`, outside every library target, so the rejected
program never affects the library build.
-/
import Lean
import Cap.Core

open Lean Meta Elab Command Term

namespace Cap

/-- A surface command: the deep language's constructors without the positivity
arguments of `splitFraction`, which the elaborator supplies. -/
declare_syntax_cat capCmd

syntax "write " term:max term:max : capCmd
syntax "splitAt " term:max term:max term:max term:max : capCmd
syntax "splitFraction " term:max term:max term:max term:max term:max : capCmd
syntax "nop" : capCmd

/-- A checked capability program: the owner, the budget denominator and a
sequence of surface commands. -/
syntax (name := ownProg) "#own_prog " term:max term:max "{" capCmd* "}" : command

/-- Elaborate one surface command to a deep `Cmd` expression. -/
private def elabCapCmd : Syntax → TermElabM Expr
  | `(capCmd| write $id:term $i:term) => do
    let idE ← elabTermEnsuringType id (mkConst ``CapId)
    let iE ← elabTermEnsuringType i (mkConst ``Nat)
    pure (mkApp2 (mkConst ``Cmd.write) idE iE)
  | `(capCmd| splitAt $id:term $id1:term $id2:term $k:term) => do
    let idE ← elabTermEnsuringType id (mkConst ``CapId)
    let id1E ← elabTermEnsuringType id1 (mkConst ``CapId)
    let id2E ← elabTermEnsuringType id2 (mkConst ``CapId)
    let kE ← elabTermEnsuringType k (mkConst ``Nat)
    pure (mkAppN (mkConst ``Cmd.splitAt) #[idE, id1E, id2E, kE])
  | `(capCmd| splitFraction $id:term $id1:term $id2:term $q1:term $q2:term) => do
    let idE ← elabTermEnsuringType id (mkConst ``CapId)
    let id1E ← elabTermEnsuringType id1 (mkConst ``CapId)
    let id2E ← elabTermEnsuringType id2 (mkConst ``CapId)
    let q1E ← elabTermEnsuringType q1 (mkConst ``Nat)
    let q2E ← elabTermEnsuringType q2 (mkConst ``Nat)
    let p1Ty ← mkAppM ``LT.lt #[mkNatLit 0, q1E]
    let p2Ty ← mkAppM ``LT.lt #[mkNatLit 0, q2E]
    let p1 ← elabTermEnsuringType (← `(by decide)) p1Ty
    let p2 ← elabTermEnsuringType (← `(by decide)) p2Ty
    pure (mkAppN (mkConst ``Cmd.splitFraction) #[idE, id1E, id2E, q1E, q2E, p1, p2])
  | `(capCmd| nop) => pure (mkConst ``Cmd.nop)
  | stx => throwError "unrecognised capability command: {stx}"

/-- Run the executable checker on the elaborated program at elaboration time. -/
private def runCheck (oE dE : Expr) (cmds : Array Expr) : TermElabM Expr := do
  let nil := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Cmd)
  let listE := cmds.foldr
    (fun c acc => mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Cmd) c acc) nil
  let runE := mkApp3 (mkConst ``Cap.check) oE dE listE
  withTransparency .all (whnf runE)

elab_rules : command
  | `(command| #own_prog $o:term $d:term { $cmds:capCmd* }) => do
    let result ← liftTermElabM do
      let oE ← elabTermEnsuringType o (mkConst ``Owner)
      let dE ← elabTermEnsuringType d (mkConst ``Nat)
      let mut es : Array Expr := #[]
      for c in cmds do
        es := es.push (← elabCapCmd c)
      runCheck oE dE es
    if result.isAppOf ``Except.ok then
      logInfo "capability program accepted"
    else if result.isAppOf ``Except.error then
      let msg ← liftTermElabM (withTransparency .all (whnf result.getAppArgs.back!))
      throwError "capability program refused: {msg}"
    else
      throwError "capability program did not evaluate to a checker result: {result}"

/-- Proof-producing form for a program written in the deep command list: elaborate
`theorem n : Checked o D cs := by unfold Checked; decide` through the ordinary
command elaborator, so the kernel checks the certificate. A refused program makes
`decide` fail, which is a compile error. -/
syntax (name := ownCert) "#own_cert " ident " : " term:max term:max ":=" term:max : command

elab_rules : command
  | `(command| #own_cert $n:ident : $o:term $d:term := $cs:term) => do
    let thm ← `(theorem $n : Checked $o $d $cs := by unfold Checked; decide)
    elabCommand thm

/-- Translate a surface command to the deep command term syntax. -/
private def capCmdToTerm : Syntax → TermElabM Syntax
  | `(capCmd| write $id:term $i:term) => `(Cmd.write $id $i)
  | `(capCmd| splitAt $id:term $id1:term $id2:term $k:term) =>
    `(Cmd.splitAt $id $id1 $id2 $k)
  | `(capCmd| splitFraction $id:term $id1:term $id2:term $q1:term $q2:term) =>
    `(Cmd.splitFraction $id $id1 $id2 $q1 $q2 (by decide) (by decide))
  | `(capCmd| nop) => `(Cmd.nop)
  | stx => throwError "unrecognised capability command: {stx}"

/-- Proof-producing surface form: translate the commands to the deep list syntax,
then declare `theorem n : Checked o D [..] := by unfold Checked; decide`, which the
ordinary command elaborator and the kernel check. -/
syntax (name := ownCertSurface) "#own_cert " ident " : " term:max term:max "{" capCmd* "}" : command

elab_rules : command
  | `(command| #own_cert $n:ident : $o:term $d:term { $cmds:capCmd* }) => do
    let terms ← liftTermElabM do
      let mut ts : Array Syntax := #[]
      for c in cmds do
        ts := ts.push (← capCmdToTerm c)
      pure ts
    let rec mkList : List (TSyntax `term) → TermElabM (TSyntax `term)
      | [] => `([])
      | x :: xs => do
        let rest ← mkList xs
        `($x :: $rest)
    let listStx ← liftTermElabM (mkList (terms.toList.map (fun s => ⟨s⟩)))
    let thm ← `(theorem $n : Checked $o $d $listStx := by unfold Checked; decide)
    elabCommand thm

/-! ## A checked program

The owner is one 64-byte read--write leaf of share 64; the program splits it in
half at 32, writes in both halves, then splits the left half into shares 32 and
32. Every command is accepted. -/

/-- One 64-byte allocation with a single read--write root leaf. -/
def surfaceOwner : Owner :=
  Owner.init ⟨0⟩ 64 64 (by decide) ⟨0⟩ ⟨1⟩

#own_prog surfaceOwner 64 {
  splitAt ⟨0⟩ ⟨2⟩ ⟨3⟩ 32
  write ⟨2⟩ 5
  write ⟨3⟩ 40
  splitFraction ⟨2⟩ ⟨4⟩ ⟨5⟩ 32 32
  nop
}

#own_cert surfaceCert : surfaceOwner 64 {
  splitAt ⟨0⟩ ⟨2⟩ ⟨3⟩ 32
  write ⟨2⟩ 5
  write ⟨3⟩ 40
}

#check surfaceCert

end Cap
