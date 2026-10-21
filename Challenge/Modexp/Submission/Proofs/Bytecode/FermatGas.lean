import Challenge.Modexp.Submission.Proofs.Bytecode.FermatMath
import Challenge.Modexp.Submission.Proofs.Bytecode.FermatNext
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FermatGas

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open HistoricalSearch
open WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOnePositive

def withModulus (template : State) (input : ByteArray) (tail : List UInt256)
    (pc : UInt256) : State :=
  WindowTwentyOneEntry.framed (context template input) pc
    (WindowTwentyOneInput.modulusWord input :: coreStack input tail)

/-- The join point at 33 with the core frame. -/
def joinState (template : State) (input : ByteArray) (tail : List UInt256) : State :=
  withModulus template input tail (UInt256.ofNat 33)

private def fermatHandled {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (hcall : template.callStack = []) (input : ByteArray) (tail : List UInt256) (htail : tail.length ≤ 590)
    (hmatch : WindowTwentyOneInput.Matches input)
    (hbn : FermatProgram.bn.toNat.Prime) (hsecp : FermatProgram.secp.toNat.Prime)
    (he : (FermatNext.fermatDiff (WindowTwentyOneInput.modulusWord input)
      (WindowTwentyOneInput.exponentWord input)).toNat = 0)
    (hprime : (FermatProgram.primeValue (WindowTwentyOneInput.modulusWord input)).toNat ≠ 0) :
    ∃ final : State, Nonempty (GasSteps (withModulus template input tail 9809) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let ec := WindowTwentyOneGasRoute.context_env template env input
  let m := WindowTwentyOneInput.modulusWord input
  let e := WindowTwentyOneInput.exponentWord input
  have hmNat : m.toNat = WindowTwentyOneInput.modulusValue input :=
    WindowTwentyOneInput.modulusWord_toNat input
  have hp : (WindowTwentyOneInput.modulusValue input).Prime := by
    rw [← hmNat]
    rcases (FermatProgram.primeValue_nonzero m).mp hprime with h | h
    · rw [h]
      exact hbn
    · rw [h]
      exact hsecp
  have heq : m - UInt256.ofNat 1 = e := FermatNext.fermatDiff_zero m e he
  have hsub : (m - UInt256.ofNat 1).toNat = m.toNat - 1 := by
    have hm1 : 1 ≤ m.toNat := by have := hp.two_le; omega
    conv_lhs => rw [Word.word_eq_ofNat_toNat m]
    rw [Word.ofNat_sub_ofNat hm1 m.val.isLt, Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have hb : m.toNat < 2^256 := m.val.isLt; omega)
  have hexponent : WindowTwentyOneInput.exponentValue input =
      WindowTwentyOneInput.modulusValue input - 1 := by
    have h := congrArg UInt256.toNat heq
    rw [hsub, WindowTwentyOneInput.exponentWord_toNat, hmNat] at h
    exact h.symm
  let final := WindowTwentyOneReturn.returned (context template input) (UInt256.ofNat 9817)
    (FermatMath.resultWord input) 0 (coreStack input tail)
  have hr := FermatProgram.run_return (context template input) m (shiftWord input)
    (coreStack input tail) (by simp [coreStack]; omega) rfl rfl
  change WindowTwentyOneMsize.runInstructionsX FermatProgram.returnProgram
    (withModulus template input tail (UInt256.ofNat 9809)) = some final at hr
  have resultSteps : GasSteps (withModulus template input tail (UInt256.ofNat 9809)) final :=
    WindowTwentyOneMsize.Block.stepsX paths.result (ec.transfer rfl rfl) rfl hr
  refine ⟨final, ⟨resultSteps⟩, ?_, ?_⟩
  · change (true && template.callStack.isEmpty) = true
    rw [hcall]
    rfl
  · have h := WindowTwentyOneReturn.returned_result (context template input)
      (UInt256.ofNat 9817) (FermatMath.resultWord input) 0 (coreStack input tail)
    rw [← FermatMath.result_spec input hmatch hp hexponent] at h
    exact h

private def inverseHandled {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (hcall : template.callStack = []) (input : ByteArray) (tail : List UInt256) (htail : tail.length ≤ 590)
    (hmatch : WindowTwentyOneInput.Matches input)
    (hm : WindowTwentyOneInput.modulusWord input = FermatProgram.bn)
    (he : (FermatNext.fermatDiff (WindowTwentyOneInput.modulusWord input)
      (WindowTwentyOneInput.exponentWord input)).toNat = 1) :
    ∃ final : State, Nonempty (GasSteps (withModulus template input tail 9858) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let ec := WindowTwentyOneGasRoute.context_env template env input
  let m := WindowTwentyOneInput.modulusWord input
  let e := WindowTwentyOneInput.exponentWord input
  let b := shiftWord input
  let final := FixedExponentProgram.finalState (context template input) 9858 b m e tail
  have hr := FixedExponentProgram.run_program (context template input) 9858 b m e tail htail
  change runInstructions FixedExponentProgram.program
    (withModulus template input tail 9858) = some final at hr
  have steps : GasSteps (withModulus template input tail 9858) final :=
    paths.inverse.steps (ec.transfer rfl rfl) rfl hr
  refine ⟨final, ⟨steps⟩, ?_, ?_⟩
  · change (true && template.callStack.isEmpty) = true
    rw [hcall]
    rfl
  · have heq := FermatNext.fermatDiff_one m e he
    have heWord : e = UInt256.ofNat
        21888242871839275222246405745257275088696311157297823662689037894645226208581 := by
      rw [←heq,show m = FermatProgram.bn from hm]
      decide
    have heNat : WindowTwentyOneInput.exponentValue input =
        21888242871839275222246405745257275088696311157297823662689037894645226208581 := by
      rw [←WindowTwentyOneInput.exponentWord_toNat input]
      change e.toNat = _
      rw [heWord]
      rfl
    have hmPos : 0 < m.toNat := by rw [show m = FermatProgram.bn from hm]; decide
    have hbNat : b.toNat = WindowTwentyOneInput.baseValue input :=
      WindowTwentyOneInput.baseWord_toNat_of_le input hmatch.1
    have hmNat : m.toNat = WindowTwentyOneInput.modulusValue input :=
      WindowTwentyOneInput.modulusWord_toNat input
    have result := WindowTwentyOneReturn.returned_result
      (FixedExponentProgram.resultTemplate (context template input) b m)
      (advancePC 1056 9858) (FixedExponent.value b m) 8 ([e,b] ++ tail)
    change final.toResult = .returned (Precompile.natToBytes (FixedExponent.value b m).toNat 32) at result
    rw [FixedExponent.value_toNat b m hmPos,hbNat,hmNat] at result
    rw [WindowTwentyOneInput.spec_eq input hmatch,heNat,Algorithm.modPow_eq,
      if_neg (show WindowTwentyOneInput.modulusValue input ≠ 0 by rw [←hmNat]; omega)]
    exact result

/-- Boundary facts choose an existing Fermat result, fixed inversion ladder, or complete window fallback. -/
def handled {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (legacy : WindowTwentyOneGasRoute.Paths artifact fork)
    (template : State) (env : Environment artifact fork template) (hcall : template.callStack = [])
    (input : ByteArray) (tail : List UInt256) (htail : tail.length ≤ 590)
    (hmatch : WindowTwentyOneInput.Matches input)
    (hbn : FermatProgram.bn.toNat.Prime) (hsecp : FermatProgram.secp.toNat.Prime) :
    ∃ final : State, Nonempty (GasSteps (joinState template input tail) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let ec := WindowTwentyOneGasRoute.context_env template env input
  let m := WindowTwentyOneInput.modulusWord input
  let e := WindowTwentyOneInput.exponentWord input
  have hjump : Decode.isValidJumpDest (context template input).executionEnv.code 745 = true := by
    rw [ec.code]; exact paths.routeJump
  have htailjump : Decode.isValidJumpDest (context template input).executionEnv.code 9800 = true := by
    rw [ec.code]; exact paths.tailJump
  have hinvjump : Decode.isValidJumpDest (context template input).executionEnv.code 9818 = true := by
    rw [ec.code]; exact paths.inverseJump
  have hraw := FermatNext.run_join (context template input) m e (shiftWord input :: tail)
    (by simp; omega) hjump
  obtain ⟨oldFinal, ⟨oldTrace⟩, oldDone, oldResult⟩ :=
    WindowTwentyOneGasRoute.handled legacy template env hcall input tail htail hmatch
  by_cases hs : (FermatNext.fermatDiff m e).toNat ≤ 1
  · rw [if_pos hs] at hraw
    have joinSteps : GasSteps (joinState template input tail) (withModulus template input tail 45) :=
      paths.join.steps (ec.transfer rfl rfl) rfl hraw
    have hpraw := FermatNext.run_prime (context template input) m (coreStack input tail)
      (by simp [coreStack]; omega) htailjump
    by_cases hp : (FermatProgram.primeValue m).toNat = 0
    · rw [if_pos hp] at hpraw
      have primeSteps : GasSteps (withModulus template input tail 45) (withModulus template input tail 94) :=
        paths.prime.steps (ec.transfer rfl rfl) rfl hpraw
      have hjraw := FermatNext.run_jumpTail (context template input) (m :: coreStack input tail)
        (by simp [coreStack]; omega) hjump
      have jumpSteps : GasSteps (withModulus template input tail 94)
          (WindowTwentyOneGasRoute.entryState template input tail) :=
        paths.jumpTail.steps (ec.transfer rfl rfl) rfl hjraw
      exact ⟨oldFinal, ⟨((joinSteps.trans primeSteps).trans jumpSteps).trans oldTrace⟩, oldDone, oldResult⟩
    · rw [if_neg hp] at hpraw
      have primeSteps : GasSteps (withModulus template input tail 45) (withModulus template input tail 9800) :=
        paths.prime.steps (ec.transfer rfl rfl) rfl hpraw
      have commonSteps := joinSteps.trans primeSteps
      have htraw := FermatNext.run_tail (context template input) m e (shiftWord input :: tail)
        (by simp; omega) hs hp hinvjump
      by_cases he : (FermatNext.fermatDiff m e).toNat = 0
      · rw [if_pos he] at htraw
        have tailSteps : GasSteps (withModulus template input tail 9800) (withModulus template input tail 9809) :=
          paths.tail.steps (ec.transfer rfl rfl) rfl htraw
        obtain ⟨final, ⟨trace⟩, done, result⟩ :=
          fermatHandled paths template env hcall input tail htail hmatch hbn hsecp he hp
        exact ⟨final, ⟨(commonSteps.trans tailSteps).trans trace⟩, done, result⟩
      · have he1 : (FermatNext.fermatDiff m e).toNat = 1 := by omega
        rw [if_neg he] at htraw
        have tailSteps : GasSteps (withModulus template input tail 9800) (withModulus template input tail 9818) :=
          paths.tail.steps (ec.transfer rfl rfl) rfl htraw
        have higraw := FermatNext.run_inverseGuard (context template input) m (coreStack input tail)
          (by simp [coreStack]; omega) hjump
        by_cases hi : (FermatNext.inverseDiff m).toNat = 0
        · rw [if_pos hi] at higraw
          have guardSteps : GasSteps (withModulus template input tail 9818) (withModulus template input tail 9858) :=
            paths.inverseGuard.steps (ec.transfer rfl rfl) rfl higraw
          have hm : m = FermatProgram.bn := FermatNext.inverseDiff_zero m hi
          obtain ⟨final, ⟨trace⟩, done, result⟩ :=
            inverseHandled paths template env hcall input tail htail hmatch hm he1
          exact ⟨final, ⟨((commonSteps.trans tailSteps).trans guardSteps).trans trace⟩, done, result⟩
        · rw [if_neg hi] at higraw
          have guardSteps : GasSteps (withModulus template input tail 9818)
              (WindowTwentyOneGasRoute.entryState template input tail) :=
            paths.inverseGuard.steps (ec.transfer rfl rfl) rfl higraw
          exact ⟨oldFinal, ⟨((commonSteps.trans tailSteps).trans guardSteps).trans oldTrace⟩, oldDone, oldResult⟩
  · rw [if_neg hs] at hraw
    have joinSteps : GasSteps (joinState template input tail) (WindowTwentyOneGasRoute.entryState template input tail) :=
      paths.join.steps (ec.transfer rfl rfl) rfl hraw
    exact ⟨oldFinal, ⟨joinSteps.trans oldTrace⟩, oldDone, oldResult⟩

/-- The fast entry at 24 (base size 32) builds the join frame with the unshifted base word. -/
def fastSteps {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (template : State)
    (env : Environment artifact fork template) (input : ByteArray)
    (hb : baseSize input = 32) :
    GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 24) [])
      (joinState template input []) := by
  have hraw := FermatNext.run_fast (context template input) [] (by simp)
  have hj : joinState template input [] =
      WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 33)
        [MachineState.readWord (context template input).executionEnv.calldata 160,
          MachineState.readWord (context template input).executionEnv.calldata 128,
          MachineState.readWord (context template input).executionEnv.calldata 96] := by
    have hs : UInt256.shiftRight (MachineState.readWord input 96) (UInt256.ofNat 0) =
        MachineState.readWord input 96 := by
      apply Word.word_ext
      rw [Word.shiftRight_toNat _ (by norm_num)]
      simp
    simp only [joinState, withModulus, coreStack, shiftWord, WindowTwentyOneInput.modulusWord,
      WindowTwentyOneInput.exponentWord, WindowTwentyOneInput.baseWord, hb, Nat.sub_self,
      Nat.zero_mul, hs]
    rfl
  rw [hj]
  exact paths.fast.steps ((WindowTwentyOneGasRoute.context_env template env input).transfer rfl rfl)
    rfl hraw

/-- The general-width entry at 101 with a base size up to 32 builds the join frame
with the base word shifted by `8 * (32 - baseSize)` and leaves `32 - baseSize` under it. -/
def genSteps {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (template : State)
    (env : Environment artifact fork template) (input : ByteArray)
    (hb : baseSize input ≤ 32) (rest : List UInt256) (hrest : rest.length ≤ 980) :
    GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 101) rest)
      (joinState template input (UInt256.ofNat (32 - baseSize input) :: rest)) := by
  let ec := WindowTwentyOneGasRoute.context_env template env input
  have h238 : Decode.isValidJumpDest (context template input).executionEnv.code 219 = true := by
    rw [ec.code]
    exact paths.bigJump
  have h31 : Decode.isValidJumpDest (context template input).executionEnv.code 33 = true := by
    rw [ec.code]
    exact paths.joinJump
  have hword : MachineState.readWord (context template input).executionEnv.calldata 0 =
      UInt256.ofNat (baseSize input) := rfl
  have hbig : baseSize input < 2 ^ 256 := by omega
  have hgt : (UInt256.gt (UInt256.ofNat (baseSize input)) (UInt256.ofNat 32)).toNat = 0 := by
    unfold UInt256.gt
    rw [Word.word_toNat_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hbig,
      Nat.mod_eq_of_lt (by norm_num : 32 < 2 ^ 256)]
    simp [Nat.not_lt.mpr hb]
  have hc := FermatNext.run_gen_check (context template input) rest (by omega) h238
  rw [hword, if_pos hgt] at hc
  have hl := FermatNext.run_gen_load (context template input) (UInt256.ofNat (baseSize input)) rest
    (by omega) h31
  have hsub := Word.ofNat_sub_ofNat hb (by decide : 32 < 2 ^ 256)
  have hshift : UInt256.shiftLeft (UInt256.ofNat 32 - UInt256.ofNat (baseSize input))
      (UInt256.ofNat 3) = UInt256.ofNat ((32 - baseSize input) * 8) := by
    rw [hsub, Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
    congr 1
  have hm160 : UInt256.ofNat 160 - UInt256.ofNat (32 - baseSize input) =
      UInt256.ofNat (96 + baseSize input + 32) := by
    rw [Word.ofNat_sub_ofNat (by omega) (by decide : 160 < 2 ^ 256)]
    congr 1
    omega
  have he128 : UInt256.ofNat 128 - UInt256.ofNat (32 - baseSize input) =
      UInt256.ofNat (96 + baseSize input) := by
    rw [Word.ofNat_sub_ofNat (by omega) (by decide : 128 < 2 ^ 256)]
    congr 1
    omega
  have hmn : (UInt256.ofNat (96 + baseSize input + 32)).toNat = 96 + baseSize input + 32 := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hen : (UInt256.ofNat (96 + baseSize input)).toNat = 96 + baseSize input := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hshift, hsub, hm160, he128, hmn, hen] at hl
  have hbw : UInt256.shiftRight (MachineState.readWord (context template input).executionEnv.calldata 96)
      (UInt256.ofNat ((32 - baseSize input) * 8)) = shiftWord input := rfl
  rw [hbw] at hl
  have gc : GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 101) rest)
      (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 112)
        (UInt256.ofNat (baseSize input) :: UInt256.ofNat 32 :: rest)) :=
    paths.genCheck.steps (ec.transfer rfl rfl) rfl hc
  have gl : GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 112)
        (UInt256.ofNat (baseSize input) :: UInt256.ofNat 32 :: rest))
      (joinState template input (UInt256.ofNat (32 - baseSize input) :: rest)) :=
    paths.genLoad.steps (ec.transfer rfl rfl) rfl hl
  exact gc.trans gl

end Challenge.Modexp.Submission.Proofs.Bytecode.FermatGas
