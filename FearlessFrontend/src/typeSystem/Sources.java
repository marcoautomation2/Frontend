package typeSystem;

import static offensiveUtils.Require.*;
import java.util.*;
import java.util.stream.Stream;

import core.B;
import core.E.Literal;
import core.M;
import core.MName;
import core.RC;
import core.Sig;
import core.T;
import inject.TypeRename;
import utils.OneOr;
import utils.Streams;

class Sources {
//l.cs() is already the fully flattened, fully substituted transitive ancestor set (Methods.expandDeclaration
//builds it that way before type checking runs), so every ancestor's own-declared signatures are reachable
//in one hop from l; recursing into each ancestor's own (already flattened) cs() would just revisit the same
//ancestors again once per path to them.
  static List<Sig> collect(TypeSystem ts, Literal l){//Note: this uses l instead of D[Ts] since more direct/efficient
    List<Sig> sources= new ArrayList<>();
    for(T.C parent : l.cs()){
      Literal parentDef= ts.decs().apply(parent.name());
      List<String> parentXs= parentDef.bs().stream().map(B::x).toList();
      for (M m : parentDef.ms()){
        if (!m.sig().origin().equals(parentDef.name())){ continue; }
        Sig canonical= findCanonical(l, m.sig().m(), m.sig().rc());
        sources.add(instantiate(m.sig(), parentXs, parent.ts(), canonical.bs()));
      }
    }
    for (M m : l.ms()){ if (m.sig().origin().equals(l.name())){ sources.add(m.sig()); } }
    assert unionCount(ts,l) == sources.size();
    assert sources.stream().allMatch(s->l.ms().stream().anyMatch(m->m.sig().m().equals(s.m()) && m.sig().rc() == s.rc()));
    assert l.ms().stream().map(M::sig).allMatch(s->sources.stream().anyMatch(si->
      si.m().equals(s.m()) && si.rc().equals(s.rc())
      )):
      l.ms().stream().map(M::sig).toList()+" @@ "+sources;
    return sources;
  }
  private static long unionCount(TypeSystem ts, Literal l){
    return supers(ts,l).flatMap(li->
      li.ms().stream().map(M::sig).filter(s->s.origin().equals(li.name()))
    ).count();
  }
  private static Stream<Literal> supers(TypeSystem ts, Literal l){
    return Stream.concat(Stream.of(l), l.cs().stream().map(T.C::name).map(ts.decs()::apply));
  }
  private static Sig findCanonical(Literal l, MName name, RC rc){
    return OneOr.of("Methods with duplicates or absent",l.ms().stream().map(M::sig).filter(s->
      s.m().equals(name) && s.rc() == rc));
  }
  private static Sig instantiate(Sig s, List<String> xs, List<T> ts, List<B> canonical){
    assert eq(s.bs().size(), canonical.size(), "Generic arity mismatch in instantiate");
    List<String> mapXs= new ArrayList<>();
    List<T> mapTs= new ArrayList<>();
    List<String> methodVars= new ArrayList<>();
    Streams.zip(s.bs(),canonical).forEach((b,c)->{
      String sourceVar= b.x();
      methodVars.add(sourceVar);
      mapXs.add(sourceVar);
      mapTs.add(new T.X(c.x(),s.span()));
    });
    Streams.zip(xs,ts).forEach((x,t)->{
      mapXs.add(x);
      mapTs.add(t);
    });
    var newTs= TypeRename.ofT(s.ts(), mapXs, mapTs);
    var newRet= TypeRename.of(s.ret(), mapXs, mapTs);
    return new Sig(s.rc(), s.m(), canonical, newTs, newRet, s.origin(), s.abs(), s.span());
  }
}