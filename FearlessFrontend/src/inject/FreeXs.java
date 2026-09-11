package inject;

import java.util.List;
import java.util.Optional;
import java.util.stream.Stream;

import core.B;
import inference.E;
import inference.IT;
import inference.M;
import inference.E.*;
import inference.Gamma;
import utils.Streams;

public record FreeXs(Gamma g){
  Stream<String> ftvE(E e){ return switch (e){
    case X x ->Stream.concat(ftvT(x.t()),g.getOpt(x.name()).map(this::ftvT).orElse(Stream.of()));
    case Literal l -> ftvL(l);
    //Used to be l.bs().stream().map(b->b.x()); with comment //Correct since bs will contain all the ftv found anywhere in the literal
    //This is not correct because of inference order: we may have not inferred the l.bs() yet!
    case Call(var ei, _,_, var targs, var es,_,_,_) -> Streams.of(ftvE(ei),ftvTs(targs),ftvEs(es));
    case ICall(var ei,_, var es,_,_,_) -> Stream.concat(ftvE(ei),ftvEs(es));
    case Type(var t,_,_,_) -> ftvT(t);
  };}
  private Stream<String> ftvL(Literal l){
    return Streams.of(l.bs().stream().map(b->b.x()), ftvCs(l.cs()), ftvMs(l.ms()));
  }
  private Stream<String> ftvM(M m){
    List<String> domBs= m.sig().bs().map(bs->dom(bs)).orElse(List.of());
    return Stream.concat(
      ftvS(m.sig()),
      m.impl().stream().flatMap(this::ftvI)
    ).filter(x->!domBs.contains(x));
  }
  List<String> dom(List<B> bs){ return bs.stream().map(b->b.x()).toList(); }
  Stream<String> ftvS(M.Sig m){ return Stream.concat(ftvOTs(m.ts()),ftvT(m.ret())); }
  Stream<String> ftvI(M.Impl m){ return ftvE(m.e()); }
  Stream<String> ftvT(Optional<IT> o){ return o.map(t->ftvT(t)).orElse(Stream.of()); }
  public Stream<String> ftvT(IT t){ return switch (t){
    case IT.X x -> Stream.of(x.name());
    case IT.RCX(_, var x) -> Stream.of(x.name());
    case IT.ReadImmX(var x) -> Stream.of(x.name());
    case IT.RCC(_, var c,_) -> ftvTs(c.ts());
    case IT.U.Instance -> Stream.of();
  };}
  public Stream<String> ftvCs(List<IT.C> cs){ return cs.stream().flatMap(c -> ftvTs(c.ts())); }
  public Stream<String> ftvEs(List<E> es){ return es.stream().flatMap(this::ftvE); }
  public Stream<String> ftvMs(List<M> ms){ return ms.stream().flatMap(this::ftvM); }
  public Stream<String> ftvOTs(List<Optional<IT>> ts){ return ts.stream().flatMap(this::ftvT); }
  public Stream<String> ftvTs(List<IT> ts){ return ts.stream().flatMap(this::ftvT); }
}