type trigger =
  | TEq of trigger_var * trigger_var
  | TIs of trigger_var * trigger_form
  | TContains of trigger_var * trigger_form
