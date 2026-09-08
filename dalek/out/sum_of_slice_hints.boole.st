program Boole;

 type choice;
 type Scalar_scalar := Sequence int;
 function Scalar_scalar_ctor (bytes : Sequence int) : Sequence int requires Sequence.length(bytes) == 32;
   {
  bytes
}
 function Scalar_scalar..bytes (bytes : Sequence int) : Sequence int {
  bytes
}
 type ctOption (T : Type);
 type Backend_Serial_U64_Scalar_scalar52 := Sequence (bv W64);
 function Backend_Serial_U64_Scalar_scalar52_ctor (limbs : Sequence (bv W64)) : Sequence (bv W64) requires Sequence.length(limbs) == 5;
   {
  limbs
}
 function Backend_Serial_U64_Scalar_scalar52..limbs (limbs : Sequence (bv W64)) : Sequence (bv W64) {
  limbs
}
 function Specs_Core_specs_u8_32_as_nat (bytes : Sequence int) : int requires Sequence.length(bytes) == 32;
   {
  Sequence.select(bytes, 0) * 1 + Sequence.select(bytes, 1) * 256 + Sequence.select(bytes, 2) * 65536 + Sequence.select(bytes, 3) * 16777216 + Sequence.select(bytes, 4) * 4294967296 + Sequence.select(bytes, 5) * 1099511627776 + Sequence.select(bytes, 6) * 281474976710656 + Sequence.select(bytes, 7) * 72057594037927936 + Sequence.select(bytes, 8) * 18446744073709551616 + Sequence.select(bytes, 9) * 4722366482869645213696 + Sequence.select(bytes, 10) * 1208925819614629174706176 + Sequence.select(bytes, 11) * 309485009821345068724781056 + Sequence.select(bytes, 12) * 79228162514264337593543950336 + Sequence.select(bytes, 13) * 20282409603651670423947251286016 + Sequence.select(bytes, 14) * 5192296858534827628530496329220096 + Sequence.select(bytes, 15) * 1329227995784915872903807060280344576 + Sequence.select(bytes, 16) * 340282366920938463463374607431768211456 + Sequence.select(bytes, 17) * 87112285931760246646623899502532662132736 + Sequence.select(bytes, 18) * 22300745198530623141535718272648361505980416 + Sequence.select(bytes, 19) * 5708990770823839524233143877797980545530986496 + Sequence.select(bytes, 20) * 1461501637330902918203684832716283019655932542976 + Sequence.select(bytes, 21) * 374144419156711147060143317175368453031918731001856 + Sequence.select(bytes, 22) * 95780971304118053647396689196894323976171195136475136 + Sequence.select(bytes, 23) * 24519928653854221733733552434404946937899825954937634816 + Sequence.select(bytes, 24) * 6277101735386680763835789423207666416102355444464034512896 + Sequence.select(bytes, 25) * 1606938044258990275541962092341162602522202993782792835301376 + Sequence.select(bytes, 26) * 411376139330301510538742295639337626245683966408394965837152256 + Sequence.select(bytes, 27) * 105312291668557186697918027683670432318895095400549111254310977536 + Sequence.select(bytes, 28) * 26959946667150639794667015087019630673637144422540572481103610249216 + Sequence.select(bytes, 29) * 6901746346790563787434755862277025452451108972170386555162524223799296 + Sequence.select(bytes, 30) * 1766847064778384329583297500742918515827483896875618958121606201292619776 + Sequence.select(bytes, 31) * 452312848583266388373324160190187140051835877600158453279131187530910662656
}
 function Specs_Scalar52_specs_group_order () : int {
  7237005577332262213973186563042994240829374041602535252466099000494570602496 + 27742317777372353535851937790883648493
}
 function Specs_Scalar_specs_is_canonical_scalar (s : Scalar_scalar) : bool requires Sequence.length(Scalar_scalar..bytes(s)) == 32;
   {
  Specs_Core_specs_u8_32_as_nat(Scalar_scalar..bytes(s)) < Specs_Scalar52_specs_group_order && Sequence.select(Scalar_scalar..bytes(s), 31) <= 127
}
 function Specs_Scalar_specs_scalar_as_nat (s : Scalar_scalar) : int requires Sequence.length(Scalar_scalar..bytes(s)) == 32;
   {
  Specs_Core_specs_u8_32_as_nat(Scalar_scalar..bytes(s))
}
 function Specs_Scalar52_specs_group_canonical (n : int) : int {
  n mod Specs_Scalar52_specs_group_order
}
 function Specs_Scalar_specs_u8_32_as_group_canonical (bytes : Sequence int) : int requires Sequence.length(bytes) == 32;
   {
  Specs_Scalar52_specs_group_canonical(Specs_Core_specs_u8_32_as_nat(bytes))
}
 function Specs_Scalar_specs_scalar_as_canonical (s : Scalar_scalar) : int requires Sequence.length(Scalar_scalar..bytes(s)) == 32;
   {
  Specs_Scalar_specs_u8_32_as_group_canonical(Scalar_scalar..bytes(s))
}
 rec function Specs_Scalar_specs_sum_of_scalars (scalars : Sequence Scalar_scalar) : int requires ∀ i_elem : int :: 0 <= i_elem && i_elem < Sequence.length(scalars) ==> Sequence.length(Scalar_scalar..bytes(Sequence.select(scalars, i_elem))) == 32;
  
decreases Sequence.length(scalars)
  {
  if Sequence.length(scalars) == 0 then 0 else Specs_Scalar52_specs_group_canonical(Specs_Scalar_specs_sum_of_scalars(Sequence.subrange(scalars, 0, Sequence.length(scalars) - 1)) + Specs_Scalar_specs_scalar_as_nat(Sequence.select(scalars, Sequence.length(scalars) - 1)))
};
 axiom [Specs_Scalar_specs_sum_of_scalars_unfold]: ∀ scalars : (Sequence Scalar_scalar) :: Specs_Scalar_specs_sum_of_scalars(scalars) == (if Sequence.length(scalars) == 0 then 0 else Specs_Scalar52_specs_group_canonical(Specs_Scalar_specs_sum_of_scalars(Sequence.subrange(scalars, 0, Sequence.length(scalars) - 1)) + Specs_Scalar_specs_scalar_as_nat(Sequence.select(scalars, Sequence.length(scalars) - 1))));
 function Specs_Scalar_specs_scalar_congruent_nat (s : Scalar_scalar, n : int) : bool requires Sequence.length(Scalar_scalar..bytes(s)) == 32;
   {
  Specs_Scalar_specs_scalar_as_canonical(s) == Specs_Scalar52_specs_group_canonical(n)
}
 function Scalar_obeys_add_spec () : bool {
  false
}
 function Scalar_add_req (self : Scalar_scalar, rhs : Scalar_scalar) : bool requires Sequence.length(Scalar_scalar..bytes(self)) == 32;
   requires Sequence.length(Scalar_scalar..bytes(rhs)) == 32;
   {
  Specs_Scalar_specs_is_canonical_scalar(self) && Specs_Scalar_specs_is_canonical_scalar(rhs)
}
 function Scalar_add_spec (self : Scalar_scalar, rhs : Scalar_scalar) : Scalar_scalar;
 function Scalar_zERO () : Scalar_scalar {
  Scalar_scalar_ctor(Sequence.of_int[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
}
 procedure Scalar_add (self : Scalar_scalar, _rhs : Scalar_scalar) returns (result : Scalar_scalar)
spec {
  requires Sequence.length(Scalar_scalar..bytes(self)) == 32;
  requires Sequence.length(Scalar_scalar..bytes(_rhs)) == 32;
  ensures Sequence.length(Scalar_scalar..bytes(result)) == 32;
  requires Scalar_add_req(self, _rhs);
  ensures Scalar_obeys_add_spec ==> result == Scalar_add_spec(self, _rhs);
  ensures Specs_Scalar_specs_scalar_as_nat(result) == Specs_Scalar52_specs_group_canonical(Specs_Scalar_specs_scalar_as_nat(self) + Specs_Scalar_specs_scalar_as_nat(_rhs));
  ensures Specs_Scalar_specs_is_canonical_scalar(result);
  } {
  assume false;
};
 procedure Scalar_helpers_sum_of_slice (scalars : Sequence Scalar_scalar) returns (result : Scalar_scalar)
spec {
  requires ∀ i_elem : int :: 0 <= i_elem && i_elem < Sequence.length(scalars) ==> Sequence.length(Scalar_scalar..bytes(Sequence.select(scalars, i_elem))) == 32;
  ensures Sequence.length(Scalar_scalar..bytes(result)) == 32;
  requires ∀ i : int :: 0 <= i && i < Sequence.length(scalars) ==> Specs_Scalar_specs_is_canonical_scalar(Sequence.select(scalars, i));
  ensures Specs_Scalar_specs_scalar_as_nat(result) < Specs_Scalar52_specs_group_order;
  ensures Specs_Scalar_specs_is_canonical_scalar(result);
  ensures Specs_Scalar_specs_scalar_congruent_nat(result, Specs_Scalar_specs_sum_of_scalars(scalars));
  } {
  var sub : (Sequence Scalar_scalar);
  var tmp7 : Scalar_scalar;
  var L : int;
  var acc_val : int;
  var old_acc_val : int;
  var scalar_val : int;
  var sum_prev : int;
  var _old_acc : Scalar_scalar;
  var n : int;
  var acc : Scalar_scalar;
  assume Sequence.length(scalars) <= 18446744073709551615;
  n := Sequence.length(scalars);
  acc := Scalar_zERO;
  call Scalar_helpers_lemma_scalar_zero_properties();
  assert Sequence.length(Sequence.subrange(scalars, 0, 0)) == Sequence.length(Sequence.empty<Scalar_scalar>()) && ∀ i_ext : int :: 0 <= i_ext && i_ext < Sequence.length(Sequence.subrange(scalars, 0, 0)) ==> Sequence.select(Sequence.subrange(scalars, 0, 0), i_ext) == Sequence.select(Sequence.empty<Scalar_scalar>(), i_ext);
  assume Sequence.subrange(scalars, 0, 0) == Sequence.empty<Scalar_scalar>();
  for i : int := 0 to Sequence.length(scalars) - 1invariant Sequence.length(Scalar_scalar..bytes(acc)) == 32
  invariant i <= Sequence.length(scalars)
  invariant 0 <= i
  invariant Specs_Scalar_specs_scalar_congruent_nat(acc, Specs_Scalar_specs_sum_of_scalars(Sequence.subrange(scalars, 0, i)))
  invariant Specs_Scalar_specs_is_canonical_scalar(acc)
  invariant Specs_Scalar_specs_scalar_as_nat(acc) < Specs_Scalar52_specs_group_order
  invariant ∀ j : int :: 0 <= j && j < Sequence.length(scalars) ==> Specs_Scalar_specs_is_canonical_scalar(Sequence.select(scalars, j))
  invariant n == Sequence.length(scalars)
  {
    _old_acc := acc;
    sub := Sequence.subrange(scalars, 0, i + 1);
    assert Sequence.length(Sequence.subrange(sub, 0, i)) == Sequence.length(Sequence.subrange(scalars, 0, i)) && ∀ i_ext : int :: 0 <= i_ext && i_ext < Sequence.length(Sequence.subrange(sub, 0, i)) ==> Sequence.select(Sequence.subrange(sub, 0, i), i_ext) == Sequence.select(Sequence.subrange(scalars, 0, i), i_ext);
    assume Sequence.subrange(sub, 0, i) == Sequence.subrange(scalars, 0, i);
    call tmp7 := Scalar_add(acc, Sequence.select(scalars, i));
    
    acc := tmp7;
    L := Specs_Scalar52_specs_group_order;
    acc_val := Specs_Core_specs_u8_32_as_nat(Scalar_scalar..bytes(acc));
    old_acc_val := Specs_Core_specs_u8_32_as_nat(Scalar_scalar..bytes(_old_acc));
    scalar_val := Specs_Core_specs_u8_32_as_nat(Scalar_scalar..bytes(Sequence.select(scalars, i)));
    sum_prev := Specs_Scalar_specs_sum_of_scalars(Sequence.subrange(scalars, 0, i));
    call Arithmetic_Div_mod_lemma_mod_bound(old_acc_val + scalar_val, L);
    call Arithmetic_Div_mod_lemma_add_mod_noop(old_acc_val, scalar_val, L);
    call Arithmetic_Div_mod_lemma_add_mod_noop(sum_prev, scalar_val, L);
    call Arithmetic_Div_mod_lemma_mod_twice(sum_prev + scalar_val, L);
  }
  assert Sequence.length(Sequence.subrange(scalars, 0, n)) == Sequence.length(scalars) && ∀ i_ext : int :: 0 <= i_ext && i_ext < Sequence.length(Sequence.subrange(scalars, 0, n)) ==> Sequence.select(Sequence.subrange(scalars, 0, n), i_ext) == Sequence.select(scalars, i_ext);
  assume Sequence.subrange(scalars, 0, n) == scalars;
  result := acc;
  exit Scalar_helpers_sum_of_slice;
};
 procedure Arithmetic_Div_mod_lemma_mod_bound (x : int, m : int) returns ()
spec {
  requires 0 < m;
  ensures 0 <= x mod m && x mod m < m;
  } {
  assume false;
};
 procedure Scalar_helpers_lemma_scalar_zero_properties () returns ()
spec {
  ensures Specs_Scalar_specs_scalar_as_nat(Scalar_zERO) == 0;
  ensures Specs_Scalar_specs_scalar_as_nat(Scalar_zERO) < Specs_Scalar52_specs_group_order;
  ensures Specs_Scalar_specs_is_canonical_scalar(Scalar_zERO);
  ensures Specs_Scalar_specs_scalar_congruent_nat(Scalar_zERO, 0);
  } {
  assume false;
};
 function Seq_empty<A> () : Sequence A;
 procedure Arithmetic_Div_mod_lemma_mod_twice (x : int, m : int) returns ()
spec {
  requires m > 0;
  ensures x mod m mod m == x mod m;
  } {
  assume false;
};
 procedure Arithmetic_Div_mod_lemma_add_mod_noop (x : int, y : int, m : int) returns ()
spec {
  requires 0 < m;
  ensures (x mod m + y mod m) mod m == (x + y) mod m;
  } {
  assume false;
};
