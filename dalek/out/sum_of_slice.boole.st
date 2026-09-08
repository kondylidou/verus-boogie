program Boole;
type Scalar := Sequence int;
function Scalar_wf (s : Scalar) : bool;
axiom [Scalar_wf_def]: ∀ s : Scalar :: Scalar_wf(s) == (Sequence.length(s) == 32 && ∀ k : int :: 0 <= k && k < 32 ==> 0 <= Sequence.select!(s, k) && Sequence.select!(s, k) < 256);
function u8_32_as_nat (bytes : Sequence int) : int {
  Sequence.select!(bytes, 0) * 1 + Sequence.select!(bytes, 1) * 256 + Sequence.select!(bytes, 2) * 65536 + Sequence.select!(bytes, 3) * 16777216 + Sequence.select!(bytes, 4) * 4294967296 + Sequence.select!(bytes, 5) * 1099511627776 + Sequence.select!(bytes, 6) * 281474976710656 + Sequence.select!(bytes, 7) * 72057594037927936 + Sequence.select!(bytes, 8) * 18446744073709551616 + Sequence.select!(bytes, 9) * 4722366482869645213696 + Sequence.select!(bytes, 10) * 1208925819614629174706176 + Sequence.select!(bytes, 11) * 309485009821345068724781056 + Sequence.select!(bytes, 12) * 79228162514264337593543950336 + Sequence.select!(bytes, 13) * 20282409603651670423947251286016 + Sequence.select!(bytes, 14) * 5192296858534827628530496329220096 + Sequence.select!(bytes, 15) * 1329227995784915872903807060280344576 + Sequence.select!(bytes, 16) * 340282366920938463463374607431768211456 + Sequence.select!(bytes, 17) * 87112285931760246646623899502532662132736 + Sequence.select!(bytes, 18) * 22300745198530623141535718272648361505980416 + Sequence.select!(bytes, 19) * 5708990770823839524233143877797980545530986496 + Sequence.select!(bytes, 20) * 1461501637330902918203684832716283019655932542976 + Sequence.select!(bytes, 21) * 374144419156711147060143317175368453031918731001856 + Sequence.select!(bytes, 22) * 95780971304118053647396689196894323976171195136475136 + Sequence.select!(bytes, 23) * 24519928653854221733733552434404946937899825954937634816 + Sequence.select!(bytes, 24) * 6277101735386680763835789423207666416102355444464034512896 + Sequence.select!(bytes, 25) * 1606938044258990275541962092341162602522202993782792835301376 + Sequence.select!(bytes, 26) * 411376139330301510538742295639337626245683966408394965837152256 + Sequence.select!(bytes, 27) * 105312291668557186697918027683670432318895095400549111254310977536 + Sequence.select!(bytes, 28) * 26959946667150639794667015087019630673637144422540572481103610249216 + Sequence.select!(bytes, 29) * 6901746346790563787434755862277025452451108972170386555162524223799296 + Sequence.select!(bytes, 30) * 1766847064778384329583297500742918515827483896875618958121606201292619776 + Sequence.select!(bytes, 31) * 452312848583266388373324160190187140051835877600158453279131187530910662656
}
function group_order () : int {
  7237005577332262213973186563042994240857116359379907606001950938285454250989
}
function is_canonical_scalar (s : Scalar) : bool {
  u8_32_as_nat(s) < group_order && Sequence.select!(s, 31) <= 127
}
function scalar_as_nat (s : Scalar) : int {
  u8_32_as_nat(s)
}
function group_canonical (n : int) : int {
  n mod group_order
}
function u8_32_as_group_canonical (bytes : Sequence int) : int {
  group_canonical(u8_32_as_nat(bytes))
}
function scalar_as_canonical (s : Scalar) : int {
  u8_32_as_group_canonical(s)
}
rec function sum_of_scalars (scalars : Sequence Scalar, n : int) : int
  requires 0 <= n && n <= Sequence.length(scalars);
  decreases n
{
  if n == 0 then 0 else group_canonical(sum_of_scalars(scalars, n - 1) + scalar_as_nat(Sequence.select(scalars, n - 1)))
};
axiom [sum_of_scalars_unfold]: ∀ scalars : (Sequence Scalar), n : int :: 0 <= n && n <= Sequence.length(scalars) ==> sum_of_scalars(scalars, n) == (if n == 0 then 0 else group_canonical(sum_of_scalars(scalars, n - 1) + scalar_as_nat(Sequence.select(scalars, n - 1))));
axiom [sum_of_scalars_nat]: ∀ scalars : (Sequence Scalar), n : int :: 0 <= n && n <= Sequence.length(scalars) ==> 0 <= sum_of_scalars(scalars, n);
function scalar_congruent_nat (s : Scalar, n : int) : bool {
  scalar_as_canonical(s) == group_canonical(n)
}
function Scalar_obeys_add_spec () : bool {
  false
}
function Scalar_add_req (self : Scalar, rhs : Scalar) : bool {
  is_canonical_scalar(self) && is_canonical_scalar(rhs)
}
function Scalar_add_spec (self : Scalar, rhs : Scalar) : Scalar;
function Scalar_ZERO () : Scalar;
axiom [Scalar_ZERO_lit_0]: Sequence.length(Scalar_ZERO) == 32;
axiom [Scalar_ZERO_lit_1]: ∀ k : int :: 0 <= k && k < 32 ==> Sequence.select!(Scalar_ZERO, k) == 0;
axiom [lemma_scalar_zero_properties_ensures_0]: scalar_as_nat(Scalar_ZERO) == 0;
axiom [lemma_scalar_zero_properties_ensures_1]: scalar_as_nat(Scalar_ZERO) < group_order;
axiom [lemma_scalar_zero_properties_ensures_2]: is_canonical_scalar(Scalar_ZERO);
axiom [lemma_scalar_zero_properties_ensures_3]: scalar_congruent_nat(Scalar_ZERO, 0);
procedure Scalar_add (self : Scalar, _rhs : Scalar) returns (result : Scalar)
spec {
  requires Scalar_wf(self);
  requires Scalar_wf(_rhs);
  ensures Scalar_wf(result);
  requires Scalar_add_req(self, _rhs);
  ensures Scalar_obeys_add_spec ==> result == Scalar_add_spec(self, _rhs);
  ensures scalar_as_nat(result) == group_canonical(scalar_as_nat(self) + scalar_as_nat(_rhs));
  ensures is_canonical_scalar(result);
}
{
  assume false;
};
procedure sum_of_slice (scalars : Sequence Scalar) returns (result : Scalar)
spec {
  requires ∀ i_elem : int :: 0 <= i_elem && i_elem < Sequence.length(scalars) ==> Scalar_wf(Sequence.select(scalars, i_elem));
  ensures Scalar_wf(result);
  requires ∀ i : int :: 0 <= i && i < Sequence.length(scalars) ==> is_canonical_scalar(Sequence.select(scalars, i));
  ensures scalar_as_nat(result) < group_order;
  ensures is_canonical_scalar(result);
  ensures scalar_congruent_nat(result, sum_of_scalars(scalars, Sequence.length(scalars)));
}
{
  var n : int;
  var acc : Scalar;
  assume Sequence.length(scalars) <= 18446744073709551615;
  n := Sequence.length(scalars);
  acc := Scalar_ZERO;
  for i : int := 0 to Sequence.length(scalars) - 1
    invariant 0 <= i && i <= Sequence.length(scalars)
    invariant Scalar_wf(acc)
    invariant n == Sequence.length(scalars)
    invariant ∀ j : int :: 0 <= j && j < Sequence.length(scalars) ==> is_canonical_scalar(Sequence.select(scalars, j))
    invariant scalar_as_nat(acc) < group_order
    invariant is_canonical_scalar(acc)
    invariant scalar_as_nat(acc) == sum_of_scalars(scalars, i)
  {
    call acc := Scalar_add(acc, Sequence.select(scalars, i));
  }
  result := acc;
  exit sum_of_slice;
};
