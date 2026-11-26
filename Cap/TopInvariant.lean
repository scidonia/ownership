/-
The combined top-level invariant and the command carrier it is derived from.

`World.TopInv` is world well-formedness together with the issuance history. The
command language preserves the stronger carrier `World.CommandInv`
(`WellFormed ∧ HistoryOK ∧ LoansReady`), and `TopInv` follows by projection.
The concrete initial worlds satisfy the top-level invariant.
-/
import Cap.History
import Cap.Unified
import Cap.Runner

namespace Cap

/-- The top-level invariant: the world is well formed and its context's
issuance history is sound. -/
def World.TopInv (w : World) : Prop :=
  w.WellFormed ∧ Ctx.HistoryOK w.ctx

theorem World.topInv_wf {w : World} (h : w.TopInv) : w.WellFormed := h.1

theorem World.topInv_history {w : World} (h : w.TopInv) : Ctx.HistoryOK w.ctx := h.2

/-- The command carrier is exactly the top-level invariant together with loan
readiness. -/
theorem World.commandInv_iff {w : World} :
    w.CommandInv ↔ w.TopInv ∧ Ctx.LoansReady w.ctx := by
  constructor
  · rintro ⟨hwf, hh, hlr⟩
    exact ⟨⟨hwf, hh⟩, hlr⟩
  · rintro ⟨⟨hwf, hh⟩, hlr⟩
    exact ⟨hwf, hh, hlr⟩

/-- Every checked execution preserves the command carrier. -/
theorem checkWorld_top : ∀ (w w' : World) (cs : List UCmd),
    checkWorld w cs = .ok w' → w.CommandInv → w'.CommandInv :=
  checkWorld_commandInv

/-- The advertised `TopInv` conclusion, with loan readiness supplied. -/
theorem checkWorld_topInv : ∀ (w w' : World) (cs : List UCmd),
    checkWorld w cs = .ok w' → w.TopInv → Ctx.LoansReady w.ctx → w'.TopInv := by
  intro w w' cs h htop hlr
  exact ⟨(checkWorld_top w w' cs h ⟨htop.1, htop.2, hlr⟩).1,
    (checkWorld_top w w' cs h ⟨htop.1, htop.2, hlr⟩).2.1⟩

/-- The empty world satisfies the top-level invariant. -/
theorem World.emptyWorld_top : World.TopInv World.emptyWorld :=
  ⟨World.emptyWorld_wf, World.emptyWorld_historyOK⟩

/-- The concrete 64-byte world satisfies the top-level invariant. -/
theorem uWorld_top : uWorld.TopInv :=
  ⟨uWorld_wf, uWorld_historyOK⟩

end Cap
