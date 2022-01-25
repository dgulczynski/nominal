open Types

let rec check kind = function
  | F_Bot | F_Var _ -> kind = Prop
  | _ -> false
