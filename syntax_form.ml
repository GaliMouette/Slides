type trigger_form =
  | TVar of string
  | TArr of trigger_form * trigger_form
  | TAnd of trigger_form * trigger_form
  | TOr of trigger_form * trigger_form
  | TTop
  | TBottom
  | TDiscard
  | TMetaVar
