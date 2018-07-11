Require Import Int63.
Require Import PArray.

Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive comparison => "int" ["0" "(-1)" "1"].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive carry => "Uint63.carry" ["Uint63.C0" "Uint63.C1"].

Extract Constant int => "Uint63.t".
Extract Constant lsl => "Uint63.l_sl".
Extract Constant lsr => "Uint63.l_sr".
Extract Constant Int63Native.land => "Uint63.l_and".
Extract Constant Int63Native.lor => "Uint63.l_or".
Extract Constant Int63Native.lxor => "Uint63.l_xor".
Extract Constant add => "Uint63.add".
Extract Constant sub => "Uint63.sub". 
Extract Constant mul => "Uint63.mul".
Extract Constant mulc => "Uint63.mulc".
Extract Constant div => "Uint63.div".
Extract Constant Int63Native.mod => "Uint63.rem".
Extract Constant eqb => "Uint63.eq".
Extract Constant ltb => "Uint63.lt".
Extract Constant leb => "Uint63.le".
Extract Constant compare => "Uint63.compare".
Extract Constant head0 => "Uint63.head0".
Extract Constant tail0 => "Uint63.tail0".

Extract Constant addc => "Uint63.addc".
Extract Constant addcarryc => "Uint63.addcarryc".
Extract Constant subc => "Uint63.subc".
Extract Constant subcarryc => "Uint63.subcarryc".
Extract Constant diveucl => "Uint63.diveucl".

Extract Constant diveucl_21 => "Uint63.diveucl_21".
Extract Constant addmuldiv => "Uint63.addmuldiv".

(* Pierre que faut-il faire pour celui la *)
(* Extract Constant eqb_correct => "Uint63.eqb_correct". *)
Extract Constant foldi_cont => "Uint63.foldi_cont".
Extract Constant foldi_down_cont => "Uint63.foldi_down_cont".
Extract Constant print_int => "Uint63.print_uint".

(** Extraction of Array *)
Extract Constant array "'a" => "'a Parray.t".
Extract Constant make => "Parray.make".
Extract Constant get => "Parray.get".
Extract Constant default => "Parray.default".
Extract Constant set => "Parray.set".
Extract Constant length => "Parray.length".
Extract Constant copy => "Parray.copy".
Extract Constant reroot => "Parray.reroot".
Extract Constant init => "Parray.init".
Extract Constant map => "Parray.map".
