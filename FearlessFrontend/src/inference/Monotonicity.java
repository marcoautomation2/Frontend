package inference;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Optional;

import core.RC;
import inference.Gamma.GammaSignature;
import utils.Range;
import utils.Streams;

public final class Monotonicity{
  private static final IdentityHashMap<GammaSignature,State> states= new IdentityHashMap<>();
  private static final class State{ final HashMap<Long,ArrayList<Object>> hist= new HashMap<>(); }
  private enum K{E_T,CALL_RC,CALL_TARG,LIT_MARG,LIT_MRET}

  // Packs (kind, a, b) into one 64-bit key.
  //
  // Bit layout (high -> low):
  //   [63..48] 16 bits: kind id (K.ordinal())
  //   [47..16] 32 bits: a (unsigned, truncated to 32 bits)
  //   [15..00] 16 bits: b (unsigned, truncated to 16 bits)
  //
  // Intended usage:
  // - E.t:                 kind=E_T      a=0                 b=0
  // - Call.rc:             kind=CALL_RC  a=0                 b=0
  // - Call.targs[i]:       kind=CALL_TARG a=i                b=0
  // - Literal.ms[mi].ret:  kind=LIT_MRET a=mi                b=0
  // - Literal.ms[mi].arg[pi]:
  //                         kind=LIT_MARG a=mi               b=pi
  //
  // Limits implied by packing:
  // - kind: up to 2^16-1 distinct K values (65535) (far more than needed)
  // - a:    up to 2^32-1 (4,294,967,295)  (effectively "unbounded" for realistic code)
  // - b:    up to 2^16-1 (65535)
  //
  // If b might exceed 65535 (very unlikely: >65k params), you'd need a wider b field.
  private static long slot(K k, int a, int b){
    assert (k.ordinal() & ~0xFFFF) == 0;
    assert (b & ~0xFFFF) == 0;
    long kind= ((long)k.ordinal() & 0xFFFFL) << 48;  // 16-bit kind
    long aa  = ((long)a & 0xFFFF_FFFFL) << 16;      // 32-bit a
    long bb  = ((long)b & 0xFFFFL);                 // 16-bit b
    return kind | aa | bb;
  }

  private static boolean step(GammaSignature g, long slot, Object from, Object to, String what){
    var st= states.computeIfAbsent(g, _->new State());
    var l= st.hist.computeIfAbsent(slot, _->new ArrayList<>(4));
    if (l.isEmpty()){ l.add(from); }
    else{
      var last= l.get(l.size()-1);
      if (!(from instanceof IT.U) && !last.equals(from)){
        throw new AssertionError("Monotonicity tracker out of sync for "+what
          +"\nLast="+last+"\nFrom="+from+"\nHist="+l);
      }
    }
    if (from.equals(to)){ return true; } // after sync/init
    for (var old: l){
      if (old.equals(to)){
        throw new AssertionError("Non-monotone evolution (cycle) for "+what
          +"\nTo="+to+"\nHist="+l);
      }
    }
    l.add(to);
    return true;
  }

  public static boolean eT(GammaSignature g, Object e, Object from, Object to){
    return step(g, slot(K.E_T,0,0), from, to, "E.t "+e.getClass().getSimpleName());
  }
  public static boolean callRc(GammaSignature g, Object call, Optional<RC> from, Optional<RC> to){
    return step(g, slot(K.CALL_RC,0,0), from, to, "Call.rc "+call);
  }
  public static boolean callTarg(GammaSignature g, Object call, int i, Object from, Object to){
    return step(g, slot(K.CALL_TARG,i,0), from, to, "Call.targs["+i+"] "+call);
  }
  public static boolean litMethArg(GammaSignature g, Object lit, int mi, int pi, Object from, Object to){
    return step(g, slot(K.LIT_MARG,mi,pi), from, to, "Literal.ms["+mi+"].arg["+pi+"] "+lit);
  }
  public static boolean litMethRet(GammaSignature g, Object lit, int mi, Object from, Object to){
    return step(g, slot(K.LIT_MRET,mi,0), from, to, "Literal.ms["+mi+"].ret "+lit);
  }

  private static boolean hasLitHistory(GammaSignature g){
    var st= states.get(g);
    if (st == null){ return false; }
    int marg= K.LIT_MARG.ordinal(), mret= K.LIT_MRET.ordinal();
    for (long key: st.hist.keySet()){
      int kind= (int)(key >>> 48);
      if (kind == marg || kind == mret){ return true; }
    }
    return false;
  }
  private static boolean hasAnyKind(GammaSignature g, K k){
    var st= states.get(g);
    if (st == null){ return false; }
    int kind= k.ordinal();
    for (long key: st.hist.keySet()){
      if ((int)(key >>> 48) == kind){ return true; }
    }
    return false;
  }

  public static boolean onCallWithMore(E.Call c, Optional<RC> nextRc, List<IT> nextTargs, IT nextT){
    step(c.g(), slot(K.E_T,0,0), c.t(), nextT, "Call.t");
    step(c.g(), slot(K.CALL_RC,0,0), c.rc(), nextRc, "Call.rc");
    int oldN= c.targs().size(), newN= nextTargs.size();
    if (oldN != newN){
      // Arity repair is allowed, but only before we started tracking per-index targs.
      if (hasAnyKind(c.g(), K.CALL_TARG)){
        throw new AssertionError("Call.targs arity changed after tracking started old="+oldN+" new="+newN
          +"\ncall="+c);
      }
      for (int i : Range.of(nextTargs)){
        var ti= nextTargs.get(i);
        step(c.g(), slot(K.CALL_TARG,i,0), ti, ti, "Call.targs["+i+"] init");
      }
      return true;
    }
    Streams.zipI(c.targs(),nextTargs).forEach((i,ct,nt)->step(c.g(), slot(K.CALL_TARG,i,0), ct, nt, "Call.targs["+i+"]"));
    return true;
  }

  private static boolean litStable(List<M> ms){
    return ms.stream().allMatch(m->m.sig().m().isPresent());
  }
  private static void clearLitHistory(GammaSignature g){
    var st= states.get(g);
    if (st == null){ return; }
    int marg= K.LIT_MARG.ordinal(), mret= K.LIT_MRET.ordinal();
    st.hist.keySet().removeIf(k->{
      int kind= (int)(k.longValue() >>> 48);
      return kind == marg || kind == mret;
    });
  }

  public static boolean onLiteralWithMs(E.Literal l, List<M> nextMs){
    // Methods may be inserted/reordered while any method has no name.
    // In that phase, we DO NOT track literal method slots at all.
    if (!litStable(l.ms()) || !litStable(nextMs)){
      clearLitHistory(l.g());
      return true;
    }

    // First stable snapshot: start tracking from nextMs (not from l.ms()).
    if (!hasLitHistory(l.g())){
      for (int mi : Range.of(nextMs)){
        var nm= nextMs.get(mi);
        var nps= sigPs(nm);
        for (int pi : Range.of(nps)){
          step(l.g(), slot(K.LIT_MARG,mi,pi), nps.get(pi), nps.get(pi), "Lit.ms["+mi+"].arg["+pi+"] init");
        }
        var r= sigRet(nm);
        step(l.g(), slot(K.LIT_MRET,mi,0), r, r, "Lit.ms["+mi+"].ret init");
      }
      return true;
    }

    int oldN= l.ms().size(), newN= nextMs.size();
    if (oldN != newN){
      throw new AssertionError("Literal.ms size changed after tracking started old="+oldN+" new="+newN
        +"\noldMs="+msBrief(l.ms())+"\nnewMs="+msBrief(nextMs)
        +"\nlit="+l);
    }

    // Same size, stable names: normal monotonic tracking by index.
    for (int mi : Range.of(nextMs)){
      var om= l.ms().get(mi);
      var nm= nextMs.get(mi);
      var ops= sigPs(om);
      var nps= sigPs(nm);
      if (ops.size() != nps.size()){
        var on= mName(om);
        var nn= mName(nm);
        throw new AssertionError("Literal.ms["+mi+"] arity changed old="+ops.size()+" new="+nps.size()
          +"\noldName="+on+"\nnewName="+nn+"\nnameChanged="+!on.equals(nn)
          +"\noldSig="+om.sig()+"\nnewSig="+nm.sig()
          +"\noldMs="+msBrief(l.ms())+"\nnewMs="+msBrief(nextMs)
          +"\nlit="+l);
      }
      for (int pi : Range.of(ops)){
        step(l.g(), slot(K.LIT_MARG,mi,pi), ops.get(pi), nps.get(pi), "Lit.ms["+mi+"].arg["+pi+"] "+l);
      }
      step(l.g(), slot(K.LIT_MRET,mi,0), sigRet(om), sigRet(nm), "Lit.ms["+mi+"].ret "+l);
    }
    return true;
  }

  private static List<IT> sigPs(M m){
    return m.sig().ts().stream().map(it->it.orElse(IT.U.Instance)).toList();
  }
  private static IT sigRet(M m){
    return m.sig().ret().orElse(IT.U.Instance);
  }
  private static String mName(M m){
    return m.sig().m().map(n->n.s()).orElse("<nameToInfer>");
  }
  private static List<String> msBrief(List<M> ms){
    return ms.stream().map(m->mName(m)+"/"+sigPs(m).size()).toList();
  }
}