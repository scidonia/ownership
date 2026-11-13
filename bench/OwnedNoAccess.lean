import OwnedStatic

/-- Direct access to the payload: the field is private, so this must not elaborate. -/
#check (Owned.new #[0]).val
