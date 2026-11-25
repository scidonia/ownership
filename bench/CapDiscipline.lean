import Cap.Discipline

open Cap

#guard (Discipline.initialState.write 7).isSome

example : Discipline.State.OK Discipline.initialState :=
  Discipline.initialState_OK
