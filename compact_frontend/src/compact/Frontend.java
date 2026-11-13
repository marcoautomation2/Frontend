package compact;
import static compact.Frontend.K.*;
import static compact.Frontend.RC.*;
import static compact.Util.*;
import compact.Frontend.T.*;
import compact.Frontend.E.Call;
import java.math.*;
import java.util.*;
import java.util.function.*;
import java.util.regex.Pattern;
import java.util.stream.*;
@SuppressWarnings("serial")public interface Frontend{
  class Fail extends RuntimeException{}
  static void no(boolean b){if(b)throw new Fail();}
  static List<Literal>compile(String pk,Map<String,String>override,Map<String,String>files,List<Literal>lits){
    var other=lits.stream().collect(Collectors.toMap(Literal::name,d->d));var raw=new TreeMap<String,File>();
    files.forEach((path,content)->raw.put(path,new Parser(new Names(list(),list(),list(),null),tokens(content)).group(Parser::file)));
    var heads=filter(raw.keySet(),p->p.matches("(.*/)?_rank_[^/]*\\.[^/]*"));
    no(heads.size()!=1);var head=raw.get(heads.get(0));
    no(any(raw.values(),f->f!=head&&f.dirs!=null));
    var ds=flat(raw.values(),f->f.decs.stream());var uses=map(head.uses,Use::out);
    var names=flat(ds,d->d.owner.decs.stream());no(dup(names));var strings=map(names,N::s);
    no(any(uses,strings::contains)||any(flat(ds,d->d.owner.gen.used.stream()),x->strings.contains(x)||uses.contains(x)));
    var map=new HashMap<>(override);for(var u:head.uses){no(map.containsValue(u.in.pk()));var p=map.getOrDefault(u.in.pk(),u.in.pk());
      var in=p+"."+u.in.simple();map.put(u.out,in);no(p.equals(pk)||!any(other.keySet(),e->e.s.equals(in)));
    }var ctx=new Methods(new Pkg(pk,map,ds,new HashSet<>(names)),other);
    var res=ctx.headers();TS.check(res,other);return res;
  }
  enum RC{
    imm,mut,read,iso,mutH,readH;
    boolean sub(RC other){return this==other||other==readH||this==iso||other==read&&!isH()||this==mut&&other==mutH;}
    boolean isH(){return ordinal()>3;}boolean ro(){return this==read||this==imm;}
    boolean ii(){return this==iso||this==imm;}
    RC ri(){return ii()?imm:read;}RC h(){return this==readH?read:this==mutH?mut:this;}
  }
  record N(String s,int arity){
    N qualify(String pk){return new N(pk+"."+s,arity);}
    N arity(int arity){return new N(s,arity);}
    String pk(){return s.replaceFirst("^(?![a-z]).*|\\..*","");}
    String simple(){return s.replaceFirst("^[a-z][^.]*\\.","");}
    boolean visible(){return!simple().startsWith("_");}
  }
  record B(String x,Set<RC>caps){
    static List<String>v(List<B>b){return b==null?list():map(b,B::x);}
    static B get(List<B>b,String name){return find(b,e->e.x.equals(name));}
  }
  enum K{
    Ws("\\s+|//[^\\n]*|/\\*[^*]*\\*+(?:[^/*][^*]*\\*+)*/"),
    Arrow("->"),LP("\\("),RP("\\)"),LB("\\{"),RBId("\\}[A-Za-z0-9_]+'*"),RB("\\}"),
    LA("(?<=[A-Za-z0-9_'"+K.op+"])(?<!\\*/)\\["),RA("\\]"),
    Hole("_"),Comma(","),Semi(";"),Implicit("::"),Colon(":"),Eq("="),Quote("'"),RIcap("read/imm"),Cap("(read|mut)H?|imm|iso"),
    SF("[+-]"+K.flt),UF(K.flt),SI("[+-]"+K.nat),UI(K.nat),Str("\"[^\"\\n]*\""),Raw("`[^`\\n]*`"),
    Dot("\\._*[a-z]"+K.id),Up("(?:"+K.pk+"\\.)?_*[A-Z]"+K.id),
    Low("_*[a-z]"+K.id),Bad("'(?:(?!//|/\\*)[^'\\n\"`])*'(?![_a-z])"),Op("(?:(?!/\\*|\\*/|//)["+K.op+"])+"),
    End,Start,Curly,Square,Round;
    static final String pk="(?!(?:con|prn|aux|nul|(?:com|lpt)[1-9])(?![a-z0-9_]))[a-z][a-z0-9_]*",id="[A-Za-z0-9_]*'*",
      op="\\\\/#*\\-+%<>=!&^~?|",nat="[0-9](?:[0-9_]*[0-9])?",flt=nat+"\\."+nat+"(?:[eE][+-]?"+nat+")?(?:soft)?";
    Pattern p;
    K(String regex){p=Pattern.compile(regex);}K(){this("");}
    int match(String s,int i){var m=p.matcher(s).useTransparentBounds(true).region(i,s.length());return m.lookingAt()?m.end()-i:-1;}
  }
  static boolean matches(String input,K...ks){return any(list(ks),k->k.match(input,0)==input.length());}
  K[]heads={Up,SF,UF,SI,UI,Raw,Str};
  record Token(K kind,String content,List<Token>tokens){boolean is(K...ks){return list(ks).contains(kind);}}
  String al="0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ+-*/=<>,.;:()[]{}`'\"!?@#$%^&_|~\\ \n";
  Map<K,Map<K,K>>groups=Map.of(Start,Map.of(End,End),LP,Map.of(RP,Round),LA,Map.of(RA,Square),LB,Map.of(RB,Curly,RBId,Curly));
  static List<Token>tokens(String s){s=s.replaceFirst("^\\uFEFF","").replaceAll("[\\r\\u2028\\u2029\\u0085]","\n");
    no(s.codePoints().anyMatch(c->al.indexOf(c)<0));var res=new Vector<Token>(list(new Token(Start,"",list())));for(int i=0;i<s.length();){
      K best=null;int len=0;for(var k:K.values()){var l=k.match(s,i);if(l>len){best=k;len=l;}}no(best==null);
      var t=new Token(best,s.substring(i,i+len),list());i+=len;if(t.is(Ws))continue;
      no(t.is(Bad)||t.is(LA)&&res.getLast().is(SI,UI,SF,UF));res.add(t);
    }
    res.add(new Token(End,"",list()));var it=res.iterator();return list(tree(it,it.next()));
  }
  static Token tree(Iterator<Token>it,Token open){
    var out=new Vector<Token>(list(open));while(true){var c=it.next();
      var g=groups.get(open.kind).get(c.kind);if(g!=null){out.add(c);return new Token(g,"",out);}
      if(groups.containsKey(c.kind)){out.add(tree(it,c));continue;}no(any(groups.values(),m->m.containsKey(c.kind)));out.add(c);
    }
  }
  sealed interface P{
    record X(String name)implements P{}
    record Lit(String self,List<PM>ms)implements P{}
    record Typed(RC r,C c,Lit l)implements P{}
    record Declared(RC r,N name,List<B>b,List<C>cs,Lit l,Owner owner)implements P{}
    record Args(RC r,List<T>types){}
    record Call(P e,String name,Args y,Pat pat,List<P>es)implements P{}
    record Implicit()implements P{}
  }
  record PS(RC r,String m,List<B>b,List<Par>ps,T t){}
  record PM(PS s,P body,boolean implicit){
    PM(PS s,P body){this(s,body,body!=null&&Frontend.implicit(body));}
    int arity(){return implicit?1:s.ps.size();}
  }
  static boolean implicit(P e){return switch(e){
    case P.Implicit _->true;case P.Call c->implicit(c.e)||any(c.es,Frontend::implicit);default->false;
  };}
  record Par(Pat xp,T t){}
  sealed interface Pat{
    Stream<String>names();
    record Name(String x)implements Pat{public Stream<String>names(){return Stream.of(x);}}
    record Des(List<List<String>>extract,String id)implements Pat{
      public Stream<String>names(){return extract.stream().map(e->e.getLast().substring(1)+id);}
    }
  }

  record File(Object dirs,List<Use>uses,List<P.Declared>decs){}record Use(N in,String out){}
  record Names(List<String>v,List<String>Xs,List<String>hid,Owner owner){
    Names add(List<String>v,List<String>Xs){
      owner.vars.used.addAll(v);owner.gen.used.addAll(Xs);return new Names(push(this.v,v),push(this.Xs,Xs),hid,owner);
    }
  }
  record Key(RC r,N name){}
  class Parser{
    Names names;List<Token>tokens;int index,limit;
    Parser(Names names,List<Token>tokens){this.names=names;this.tokens=tokens;limit=tokens.size();}
    Parser make(List<Token>tokens){return new Parser(names,tokens);}
    <A>A whole(Function<Parser,A>r){var res=r.apply(this);no(!end());return res;}
    boolean end(){return limit==index;}
    boolean see(int la,K...ks){return index+la<limit&&tokens.get(index+la).is(ks);}
    boolean see(K...ks){return see(0,ks);}
    Token take(K...ks){no(end());var t=tokens.get(index++);no(ks.length>0&&!t.is(ks));return t;}
    boolean fwd(boolean v){if(v)index++;return v;}
    <A>A group(Function<Parser,A>r){
      var p=make(tokens.get(index++).tokens);p.index=1;p.limit--;return p.whole(r);
    }
    Parser front(ToIntFunction<Parser>probe){
      var sub=make(tokens.subList(index,limit));var res=make(tokens.subList(index,index-probe.applyAsInt(sub)+sub.index));index+=sub.index;return res;
    }
    <A>List<A>by(ToIntFunction<Parser>probe,Function<Parser,A>elem){var res=new Vector<A>();while(!end())res.add(front(probe).whole(elem));return res;}
    <A>List<A>items(ToIntFunction<Parser>probe,Function<Parser,A>r){return group(p->p.by(probe,r));}
    <A>A prefix(ToIntFunction<Parser>probe,Function<Parser,A>first){var i=index;var p=front(probe);if(!end())return p.whole(first);index=i;return null;}
    int so(int mode,K k){while(!end())if(take().is(k)){if(mode==2)index--;return mode&1;}return 0;}
    P expr(){return posts(atom());}P posts(P e){while(!end())e=post(e);return e;}
    boolean isDec(){return see(heads)&&(see(1,Colon)||see(1,Square)&&see(2,Colon));}
    P atom(){
      if(see(Low)){var x=take().content;no(!names.v.contains(x));return new P.X(x);}
      if(see(Round))return group(Parser::expr);
      if(fwd(see(Implicit)))return new P.Implicit();if(see(Curly))return group(p->p.literal(false));
      var r=optCap();no(r!=null&&r.isH());if(isDec())return declaration(r,false);
      return new P.Typed(or(r,imm),constructor(),see(Curly)?group(p->p.literal(false)):null);
    }
    RC cap(){return RC.valueOf(take(Cap).content);}RC optCap(){return see(Cap)?cap():null;}
    C constructor(){
      var c=name();List<T>types=see(Square)?items(comma,Parser::type):list();return new C(c.arity(types.size()),types);
    }
    N name(){var s=take(heads).content;
      var res=new N(s,0);no(!res.pk().isEmpty()&&!res.visible());return res;
    }
    T type(){
      if(fwd(see(RIcap)))return new RI(variable(false));var r=optCap();
      if(see(heads)&&!names.Xs.contains(tokens.get(index).content))return new R(or(r,imm),constructor());
      var res=variable(false);return r==null?res:new RX(r,res);
    }
    X variable(boolean mustNew){
      var c=take(Up,"[^.]*");no(mustNew?names.Xs.contains(c)||names.hid.contains(c):!names.Xs.contains(c));return new X(c);
    }
    P post(P receiver){
      if(see(SF,SI)){var num=take().content;
        return new P.Call(receiver,num.substring(0,1),null,null,list(new P.Typed(imm,new C(new N(num.substring(1),0),list()),null)));
      }
      var m=take(Dot,Op).content;var sq=see(Square)?group(Parser::arguments):null;
      if(see(Round))return new P.Call(receiver,m,sq,null,items(Parser::exprEnd,Parser::expr));
      var xpat=see(Low,Curly)&&see(1,Eq)?pattern():null;fwd(xpat!=null);
      if(xpat==null&&(end()||see(Dot,Op,Colon)))return new P.Call(receiver,m,sq,null,list());
      var atom=atom();var v=xsOf(xpat).toList();fresh(v);
      no(xpat instanceof Pat.Des&&v.size()>31);names=names.add(v,list());
      return new P.Call(receiver,m,sq,xpat,xpat==null?list(atom):list(atom,posts(post(new P.X("")))));
    }
    Pat pattern(){return see(Low)?new Pat.Name(binder()):group(Parser::destruct);}
    Pat.Des destruct(){
      var id=tokens.get(limit).content.substring(1);
      var chains=by(comma,p->p.by(q->{q.take();return 0;},q->q.take(Dot).content));
      no(chains.size()==0||any(chains,List::isEmpty));var res=new Pat.Des(chains,id);
      no(res.names().anyMatch(x->!matches(x,Low)||matches(x,Cap)));return res;
    }
    P.Args arguments(){
      var hasCap=see(Cap)&&tokens.get(index+1).is(Comma,RA);var r=hasCap?cap():null;
      if(hasCap&&!end())take(Comma);return new P.Args(r,by(comma,Parser::type));
    }
    String binder(){var x=take(Low,Hole).content;no(names.v.contains(x));return x;}
    P.Lit literal(boolean top){
      no(tokens.get(limit).is(RBId));var self=fwd(see(Quote))?binder():top?"this":"_";
      no(top&&!self.equals("this"));if(!self.equals("_"))names=names.add(list(self),list());
      var ms=by(p->p.so(1,Semi),p->p.method(top));
      var ns=map(filter(ms,m->m.s.m!=null),m->new Key(m.s.r,new N(m.s.m,m.arity())));no(dup(ns)||any(ns,nn->nn.r==null&&any(ns,o->o.name.equals(nn.name)&&o.r!=null))||dup(map(filter(ms,m->m.s.m==null),PM::arity)));return new P.Lit(self,ms);
    }
    Stream<String>xsOf(Pat xp){return Stream.ofNullable(xp).flatMap(Pat::names);}
    void fresh(List<String>v){no(dup(v)||any(v,names.v::contains));}
    PM method(boolean top){
      var s=prefix(p->p.so(1,Arrow),Parser::signature);if(s!=null){var v=flat(s.ps,p->xsOf(p.xp));fresh(v);
        names=names.add(v,B.v(s.b));var m=new PM(s,whole(Parser::expr));
        no(m.implicit&&s.ps.size()>0||any(s.ps,p->p.xp instanceof Pat.Des)&&v.size()>32);return m;
      }
      if(!(see(Dot,Op)||see(Cap)&&see(1,Dot,Op)))return new PM(new PS(null,null,null,list(),u),whole(Parser::expr));no(!top);return new PM(signature(),null);
    }
    PS signature(){
      var r=optCap();no(r!=null&&(r.isH()||r==iso));
      var m=see(Dot,Op)?take().content:null;var b=see(Square)?bounds(true):null;
      names=names.add(list(),B.v(b));
      List<Par>ps=see(Round)?items(comma,Parser::parameter):see(Colon)?list():by(comma,Parser::parameter);
      var t=fwd(see(Colon))?type():u;var v=flat(ps,p->xsOf(p.xp));
      no(dup(v));names.owner.vars.used.addAll(v);return new PS(r,m,b,ps,t);
    }
    Par parameter(){
      var named=see(Low,Hole,Curly);var x=named&&!fwd(see(Hole))?pattern():null;
      return new Par(x,named?fwd(see(Colon))?type():u:type());
    }
    List<B>bounds(boolean mustNew){var res=items(Parser::boundEnd,p->p.bound(mustNew));no(dup(B.v(res)));return res;}
    B bound(boolean mustNew){
      var x=variable(mustNew).name;if(end())return new B(x,caps(imm));take(Colon);no(end());if(!see(Op)){
        var caps=by(comma,Parser::cap);no(dup(caps));return new B(x,EnumSet.copyOf(caps));
      }
      return switch(take(Op).content){case "**"->new B(x,allRC);case "*"->new B(x,caps(imm,mut,read));default->throw new Fail();};
    }
    P.Declared declaration(RC r,boolean top){
      var c=name();no(c.s.contains(".")||primitive(c.s));
      List<B>b=see(Square)?bounds(top):list();var outer=names;var owner=top?new Owner():names.owner;
      names=new Names(names.v,list(),push(names.hid,names.Xs),owner).add(list(),B.v(b));owner.decs.add(c=c.arity(b.size()));take(Colon);
      var cs=required(prefix(p->p.so(2,Curly),p->p.by(comma,Parser::constructor)));
      var l=group(p->p.literal(top));names=outer;return new P.Declared(r,c,b,cs,l,owner);
    }
    File file(){
      var maps=new HashSet<String>();var uses=new Vector<Use>();var dirs=front(Parser::headEnd).whole(p->{
        if(!p.see(Low))return null;no(!p.tokens.get(--p.limit).is(Semi));return p.by(q->q.so(1,Semi),q->q.directive(maps,uses));
      });
      return new File(dirs,uses,by(p->p.so(0,Curly),p->p.declaration(null,true)));
    }
    String take(K kind,String regex){var s=take(kind).content;no(!s.matches(regex));return s;}
    Object directive(HashSet<String>maps,Vector<Use>uses){
      if(take(Low,"map|use").equals("map")){
        var in=take(Low,K.pk);take(Low,"as");take(Low,"_"+K.pk);
        take(Low,"in");no(!maps.add(in+" "+take(Low,"_"+K.pk)));
        if(!end()){take(Low,"instead");take(Low,"of");do take(Low,"_"+K.pk);while(!end()&&take(Comma)!=null);}
      }else{
        var a=name();take(Low,"as");
        var z=take(Up,"[^.]*");no(any(uses,u->u.in.equals(a)||u.out.equals(z)));
        uses.add(new Use(a,z));
      }return null;
    }
    int exprEnd(){var inColon=false;while(!end()){
      var t=take();if(t.is(Comma)&&!inColon)return 1;inColon=t.is(Colon)||inColon&&t.is(Square,Comma,Up);
    }return 0;}
    int boundEnd(){while(!end())if(take().is(Comma)&&!see(Cap))return 1;return 0;}
    int headEnd(){while(!(end()||isDec()))take();return 0;}
    static ToIntFunction<Parser>comma=p->p.so(1,Comma);
  }
  record Pkg(String name,Map<String,String>map,List<P.Declared>decs,Set<N>names){}
  class Scope extends HashMap<String,Integer>{HashSet<String>used=new HashSet<>();}
  class Owner{Scope gen=new Scope(),vars=new Scope();Vector<N>decs=new Vector<>();}

  N str=base("Str",0),nat=base("Nat",0),integer=base("Int",0),floating=base("Float",0),
    widen=base("WidenTo",1),sealed=base("Sealed",0),cf=base("CaptureFree",0),identity=base("BaseId",2),log=base("FileLog",0),
    container=base("BaseContainer",1),main=base("Main",0),fin=base("Final",1);
  List<N>concrete=list(base("SystemAttenuator",0),base("InfoMain",0),base("DataRead",0),log,base("InMemoryLog",1));
  List<N>claims=list(base("OpenWith",1),base("OpenWith",2),base("Shortcut",1),base("Shortcut",2),base("PreLoadIcon",1));
  static Set<RC>caps(RC first,RC...rest){return EnumSet.of(first,rest);}
  Set<RC>ii=caps(iso,imm),plain=caps(iso,imm,mut,read),allRC=EnumSet.allOf(RC.class);
  static N base(String s,int n){return new N("base."+s,n);}static boolean has(List<C>cs,N magic){return any(cs,c->c.name.equals(magic));}
  static boolean primitive(String name){return name.matches("[-+0-9\"`].*");}
  static String quoted(T t){var s=t instanceof R(_,var e)?e.name.simple():"";no(!s.matches("[\"`].*"));return s.substring(1,s.length()-1);}
  static Literal from(N n,Function<N,Literal>map,Map<N,Literal>other){
    var res=or(map.apply(n),other.get(n));var s=n.simple();
    if(res!=null||!primitive(s))return res;
    var lit=matches(s,Str,Raw)?str:matches(s,UI)?nat:matches(s,SI)?integer:floating;
    var sup=from(lit,map,other);var ms=map(sup.ms,m->m.signature(new S(m.s.r,m.s.m,m.s.b,m.s.types,m.s.t,n,false,m.s.idx)));
    return new Literal(imm,n,list(),push(new C(lit,list()),sup.cs),"this",ms,u,true,false);
  }
  T u=U.Instance;
  interface T{
    default boolean tv(){return this!=u;}
    default RC erc(){return null;}default int depth(){return 1;}
    record X(String name)implements T{}
    record RX(RC r,X x)implements T{public RC erc(){return r;}}
    record RI(X x)implements T{}
    record C(N name,List<T>types){}
    record R(RC r,C c)implements T{
      R withTs(List<T>types){return with(r,types);}
      R with(RC r,List<T>types){return new R(r,new C(c.name,types));}
      public boolean tv(){return all(c.types,T::tv);}public int depth(){return 1+c.types.stream().mapToInt(T::depth).max().orElse(1);}
      public RC erc(){return r;}
    }
    enum U implements T{Instance}
    default String v(){return switch(this){case X x->x.name;case RX(_,var x)->x.name;case RI(var x)->x.name;default->null;};}
    default T rc(RC r){return this==u?this:this instanceof R w?new R(r,w.c):new RX(r,new X(v()));}
    default Stream<String>ftv(){return this instanceof R w?typeFree(w.c.types):Stream.ofNullable(v());}
    default T ri(){return switch(this){
      case X x->new RI(x);case R(var r,var c)->new R(r==null?null:r.ri(),c);case RX(var r,var x)->new RX(r.ri(),x);default->this;
    };}
  }
  sealed interface E{
    T t();E t(T t);
    default Stream<E>children(){return switch(this){
      case Literal l->l.ms.stream().flatMap(m->Stream.ofNullable(m.e));case Call c->push(c.e,c.es).stream();default->Stream.of();
    };}
    record X(String name,T t)implements E{
      public E t(T t){return new X(name,t);}
    }
    record Call(E e,N name,RC r,List<T>y,List<E>es,T t,boolean written)implements E{
      Call children(E e,List<E>es){return new Call(e,name,r,y,es,t,written);}
      public Call t(T t){return new Call(e,name,r,y,es,t,written);}
    }
  }
  record Literal(RC r,N name,List<B>b,List<C>cs,String self,List<M>ms,T t,boolean anon,boolean expanded)implements E{
    public Literal t(T t){return new Literal(r,name,b,cs,self,ms,t,anon,expanded);}
    Literal header(List<C>cs,List<M>ms){return new Literal(r,name,b,cs,self,ms,t,anon,true);}
    R self(RC r){return new R(r,new C(name,vars(b)));}
  }
  record M(S s,List<String>v,E e){
    M(S s){this(s,Collections.nCopies(s.types.size(),"_"),null);}
    M signature(S s){return new M(s,v,e);}M body(E e){return new M(s,v,e);}
    M o(N a,N b){return Objects.equals(s.o,a)?signature(s.o(b)):this;}
  }
  record S(RC r,N m,List<B>b,List<T>types,T t,N o,boolean abs,int idx){
    S types(List<T>types,T t){return new S(r,m,b,types,t,o,abs,idx);}
    S o(N o){return new S(r,m,b,types,t,o,abs,idx);}List<T>all(){return push(types,t);}
    S subst(List<B>b,List<String>v,List<T>types){return new S(r,m,b,rename(this.types,v,types),rename(t,v,types),o,abs,idx);}
  }
  static<A>A or(A a,A b){return a==null?b:a;}
  static<A>A required(A a){no(a==null);return a;}
  record Frame(RC r,List<B>b,HashMap<String,T>vars){}
  class IG extends Vector<Frame>{
    IG(){push(null,list());}
    T get(String x){return find(map(this,f->f.vars.get(x)),t->t!=null);}
    static T adapt(T t,RC r,List<B>b){if(t==u)return t;var caps=TS.kinds(b,t);
      return r==imm||ii.containsAll(caps)?t.rc(imm):r==read||!caps(imm,mut,read).containsAll(caps)?t.ri():t;
    }
    void push(RC r,List<B>b){add(new Frame(r,b,new HashMap<>()));}
    Object declare(String x,T t){return getLast().vars.put(x,t);}
    void declare(M m){zip(m.v,m.s.types,this::declare);}
    Object snap(){return map(this,f->new HashMap<>(f.vars));}
  }
  static C normC(C c){return((R)norm(new R(null,c))).c;}
  static T norm(T t){no(!t.tv());return fill(t);}
  static int size(T t){return t instanceof R w?1+size(w.c.types.stream()):1;}
  static int size(Stream<T>s){return s.mapToInt(Frontend::size).sum();}
  static int size(E e){return size(e.t())+e.children().mapToInt(Frontend::size).sum()+switch(e){
    case Call c->size(c.y.stream());
    case Literal l->size(ts(l));default->0;
  };}
  static Stream<T>ts(Literal l){return cat(l.cs.stream().map(c->new R(null,c)),l.ms.stream().flatMap(m->m.s.all().stream()));}
  static T fill(T t){return t instanceof R(var r,var c)?new R(or(r,imm),c).withTs(map(c.types,Frontend::fill)):t;}
  static T rename(T t,List<String>v,List<T>types){
    if(t instanceof R w)return w.withTs(rename(w.c.types,v,types));
    var x=t.v();if(x==null||!v.contains(x))return t;
    var a=types.get(v.indexOf(x));
    return t instanceof RI?a.ri():t instanceof RX?a.rc(t.erc()):a;
  }
  static List<T>rename(List<T>tsi,List<String>v,List<T>types){return map(tsi,ti->rename(ti,v,types));}
  static Stream<String>typeFree(List<T>ts){return ts.stream().flatMap(T::ftv);}
  static List<T>vars(List<B>b){return map(b,e->new X(e.x));}
  static List<T>qs(int n){return Collections.nCopies(n,u);}
  record MS(RC r,List<String>v,List<B>cb,List<T>cas,List<B>mb,List<T>ps,T ret){}
  static Stream<String>free(IG g,E e){return switch(e){
    case E.X(var name,var t)->cat(t.ftv(),Stream.ofNullable(g.get(name)).flatMap(T::ftv));
    case Literal l->cat(l.b.stream().map(B::x),supFree(l.cs),methodFree(g,l.ms));
    case Call c->cat(free(g,c.e),typeFree(c.y),c.es.stream().flatMap(x->free(g,x)));
  };}
  static Stream<String>supFree(List<C>cs){return cs.stream().flatMap(c->typeFree(c.types));}
  static Stream<String>methodFree(IG g,List<M>ms){return ms.stream().flatMap(m->cat(typeFree(m.s.all()),Stream.ofNullable(m.e).flatMap(ei->free(g,ei))).filter(x->!B.v(m.s.b).contains(x)));}
  record XE(String x,P e){}
  class Methods{
    Pkg p;Map<N,Literal>other;Scope top=new Scope();HashSet<String>reserved=new HashSet<>();HashMap<N,Owner>owners=new HashMap<>();HashMap<N,Literal>cache=new HashMap<>();HashMap<N,C>sup=new HashMap<>();HashSet<String>inferred=new HashSet<>();
    int deep,cap;boolean late;N owner;Vector<String>implicits=new Vector<>();Vector<Literal>decs=new Vector<>();
    Methods(Pkg p,Map<N,Literal>other){this.p=p;this.other=other;
      top.used.addAll(map(p.names,N::simple));top.used.addAll(p.map.keySet());
      for(var d:p.decs){reserved.addAll(d.owner.gen.used);owners.put(d.name.qualify(p.name),d.owner);}
    }
    String fresh(String hint){return fresh(hint,owners.get(owner).vars,list());}
    N type(N hint,int arity){
      var res=new N(p.name+"."+fresh(hint.simple(),top,list(reserved)),arity);owners.put(res,owners.get(hint));return res;
    }
    E copy(E e){return switch(e){
      case Call c->c.children(copy(c.e),map(c.es,this::copy));
      case Literal l->{no(!l.anon);var name1=type(l.name,l.name.arity);
        yield new Literal(l.r,name1,l.b,l.cs,l.self,map(l.ms,m->m.o(l.name,name1).body(copy(m.e))),l.t,true,l.expanded);
      }
      case null,default->e;
    };}
    String fresh(String hint,Scope s,List<Collection<String>>checks){
      var base=hint.replaceAll("[^A-Za-z0-9]","").replaceFirst("(?<=.{4}).*","");var abc="abcdefghjkmnpqrstuvwxyz";if(base.matches("[A-Z].*"))abc=abc.toUpperCase();for(int n=s.getOrDefault(base,1);;n++){
        var sb="";for(int k=n;k-->0;k/=23)sb=abc.charAt(k%23)+sb;
        var cand="_"+sb+base;if(any(checks,e->e.contains(cand))||!s.used.add(cand))continue;
        s.put(base,n+1);return cand;
      }
    }
    N f(N tn){
      var pN=tn.pk();if(pN.isEmpty()&&primitive(tn.s))return tn.qualify("base");
      var full=new N(pN.isEmpty()?p.map.getOrDefault(tn.s,p.name+"."+tn.s):p.map.getOrDefault(pN,pN)+"."+tn.simple(),tn.arity);
      no(!pN.isEmpty()&&(pN.equals(p.name)||p.map.containsValue(pN)||p.map.containsValue(full.s))||!(full.pk().equals(p.name)?p.names.contains(new N(full.simple(),full.arity)):other.containsKey(full)));return full;
    }
    T type(T t){return t instanceof R(var r,var c)?new R(r,constructor(c)):t;}
    E expr(P e){return switch(e){
      case P.X x->new E.X(x.name,u);case P.Implicit _->new E.X(implicits.getLast(),u);
      case P.Typed t->literal(t.r,list(constructor(t.c)),or(t.l,new P.Lit("_",list())));
      case P.Declared c->{var name=f(c.name);owners.put(name,owners.get(owner));
        yield used(declaration(name,or(c.r,imm),c),c.l.self);
      }
      case P.Lit l->literal(null,list(),l);
      case P.Call c->{
        if(c.pat!=null){var x=fresh("eqS");c=new P.Call(c.e,c.name,c.y,null,list(c.es.get(0),lambda(list(new Par(c.pat,u),new Par(new Pat.Name(x),u)),receiver(c.es.get(1),new P.X(x)))));}var sq=or(c.y,new P.Args(null,list()));
        yield new Call(expr(c.e),new N(c.name,c.es.size()),sq.r,map(sq.types,this::type),map(c.es,this::expr),u,c.y!=null);
      }
    };}
    C constructor(C c){var s=c.name.s;
      no(matches(s,UI,SI)&&new BigInteger(s.replace("_","")).bitLength()>(matches(s,UI)?64:63));
      if(matches(s,SF,UF)){var ns=s.replace("soft","").replace("_","");var d=Double.parseDouble(ns);
        no(!Double.isFinite(d)||!s.endsWith("soft")&&(d==0?new BigDecimal(ns.replaceAll("[eE].*","")):new BigDecimal(ns).subtract(new BigDecimal(d))).signum()!=0);
      }
      return new C(f(c.name),map(c.types,this::type));
    }
    List<M>methods(List<PM>ms){return seq(ms.size(),i->method(ms.get(i),i));}
    M method(PM m,int idx){var q=m.s;var original=q.ps;var types=map(original,p->type(p.t));if(m.implicit)types=push(types,u);
      var s=new S(q.r,q.m==null?null:new N(q.m,m.arity()),q.b,types,type(q.t),null,m.body==null,idx);
      if(m.body==null)return new M(s,map(original,p->p.xp instanceof Pat.Name(var x)?x:"_"),null);var body=m.body;
      var patterns=any(original,p->p.xp instanceof Pat.Des);
      var ps=map(original,p->switch(p.xp){case null->fresh("0");case Pat.Name(var x)->patterns?fresh(x):x;case Pat.Des _->fresh("div");});
      var xpats=flat(zip(ps,original,(x,p)->switch(p.xp){
        case null->Stream.<XE>of();
        case Pat.Des d->zip(d.extract,d.names().toList(),(e,z)->{P res=new P.X(x);for(var n:e)res=new P.Call(res,n,null,null,list());return new XE(z,res);}).stream();
        case Pat.Name(var z)->Stream.of(new XE(z,new P.X(x)));
      }),y->y);if(m.implicit){
        var p=fresh("impl");ps=push(ps,p);implicits.add(p);
      }if(patterns){var w=new HashMap<String,String>();p.map.forEach((k,v)->w.put(v,k));
        var fl=lambda(map(xpats,xe->new Par(new Pat.Name(xe.x),u)),body);
        body=new P.Call(new P.Typed(imm,new C(new N(p.name.equals("base")?"Destruct":w.getOrDefault("base.Destruct",w.getOrDefault("base","base")+".Destruct"),0),list()),null),"#",null,null,push(map(xpats,XE::e),fl));
      }
      var e=expr(body);if(m.implicit)implicits.removeLast();return new M(s,ps,e);
    }
    Literal literal(RC r,List<C>impl,P.Lit l){var ms=methods(l.ms);
      return used(new Literal(r,type(owner,0),list(),impl,name(l.self),ms,u,true,false),l.self);
    }
    String name(String x){return x.equals("_")?fresh("0"):x;}
    Literal used(Literal l,String x){no(!x.equals("_")&&TS.count(x,l,false)==0);return l;}
    Literal declaration(N name,RC r,P.Declared d){var cs=map(d.cs,this::constructor);
      no(distinct(d.b,cs).size()<cs.size());
      var l=new Literal(r,name,d.b,cs,name(d.l.self),methods(d.l.ms),u,false,false);decs.add(l);return l;
    }
    P lambda(List<Par>ps,P body){return new P.Lit("_",list(new PM(new PS(null,null,null,ps,u),body,false)));}
    P receiver(P par,P atom){
      return par instanceof P.Call c?new P.Call(receiver(c.e,atom),c.name,c.y,c.pat,c.es):atom;
    }
    List<Literal>headers(){for(var di:p.decs){owner=f(di.name);declaration(owner,mut,di);}var rem=new LinkedHashMap<N,Literal>();
      decs.forEach(d->rem.put(d.name,d));var acc=new Vector<Literal>();while(rem.size()>0){
        var layer=filter(rem.values(),d->!any(d.cs,c->rem.containsKey(c.name)));
        no(layer.size()==0);for(var d:layer){
          rem.remove(d.name);register(expand(d));if(d.self.equals("this"))acc.add(cache.get(d.name));
        }
      }deep=cat(cache.values().stream(),other.values().stream()).flatMap(Frontend::ts).mapToInt(T::depth).max().orElse(1);
      return map(acc,di->di.header(di.cs,map(di.ms,m->body(di,m))));
    }
    List<C>parents(C c){var d=from(c.name);return d==null?list():d.cs.stream().map(ci->new C(ci.name,rename(ci.types,B.v(d.b),c.types))).distinct().toList();
    }
    S alpha(M m,C c,Literal child,List<String>scope){var s=m.s;var xs=new Vector<>(B.v(from(c.name).b));
      var ts=new Vector<>(c.types);var bs=new Vector<B>();var gen=owners.get(child.name).gen;for(var b:s.b){var x=b.x;
        if(!gen.used.contains(x)&&!top.used.contains(x)&&!scope.contains(x)){bs.add(b);continue;}xs.add(x);
        var next=fresh(x,gen,list(top.used,push(B.v(s.b),scope)));reserved.add(next);ts.add(new X(next));bs.add(new B(next,b.caps));
      }return s.subst(bs,xs,ts);
    }
    Literal from(N name){return Frontend.from(name,cache::get,other);}
    Literal expand(Literal d){
      var implied=flat(d.cs,c->parents(c).stream());
      var supers=distinct(d.b,push(d.cs,implied.stream().sorted(Comparator.comparing(Print::of)).toList()));
      var signatures=flat(filter(d.cs,c->!implied.contains(c)),c->from(c.name).ms.stream().map(m->alpha(m,c,d,list())));
      return magic(d.header(supers,pair(d.ms,signatures,d)),supers);
    }
    Literal magic(Literal d,List<C>supers){no(filter(supers,c->c.name.equals(widen)).size()>1);
      if(has(supers,identity)){var m=d.ms.get(0);no(d.ms.size()!=1||m.e==null&&!m.s.abs&&!has(from(m.s.o).cs,identity));}
      if(has(supers,log)){var s=d.name.simple();no(s.matches(".*('|_[a-z]).*"));var f=s.replaceAll("[A-Z]","_$0").toLowerCase(Locale.ROOT).substring(1);
        no(f.matches("con|prn|aux|nul|(com|lpt)[1-9]|_rank_.*")||f.length()+d.name.pk().length()>184);
      }
      var cl=filter(supers,c->claims.contains(c.name));no(cl.size()>0&&!has(supers,main));var exts=new HashSet<String>();
      for(var c:cl){no(!(c.types.get(0)instanceof R(_,var i)&&i.types.size()==0));if(c.types.size()==1)continue;
        var ext=quoted(c.types.get(1));
        no(!ext.matches("[a-z0-9]{1,16}")||ext.equals("fearless")||c.name.simple().equals("Shortcut")!=ext.matches("fapp[0-9]{3}")||!exts.add(ext));
      }
      for(var c:filter(supers,x->x.name.equals(fin))){var m=quoted(c.types.get(0));no(!matches(m,Dot,Op)||any(supers,o->!o.name.equals(fin)&&any(parents(o),p->p.name.equals(fin)&&quoted(p.types.get(0)).equals(m)))&&any(d.ms,mi->mi.s.m.s().equals(m)&&d.name.equals(mi.s.o)));
      }
      no(d.b.size()>0&&(has(supers,main)||any(concrete,n->has(supers,n))&&all(d.ms,m->m.e!=null||!m.s.abs))||any(supers,c->!c.name.pk().equals(d.name.pk())&&has(from(c.name).cs,sealed)));return d;
    }
    void register(Literal d){
      cache.put(d.name,new Literal(or(d.r,imm),d.name,d.b,map(d.cs,Frontend::normC),d.self,map(d.ms,m->m.signature(merge(m.s,m.s))),u,true,false));
    }
    M name(M m,Vector<S>ss){
      var arity=m.s.types.size();for(var abs:list(true,false)){
        var match=filter(ss,s->s.m.arity==arity&&(s.abs||!abs));ss.removeAll(match);
        var count=match.stream().map(S::m).distinct().count();no(count>1);if(count==1){var s=m.s;
          return m.signature(new S(s.r,match.get(0).m,s.b,s.types,s.t,s.o,s.abs,s.idx));
        }
      }throw new Fail();
    }
    List<M>pair(List<M>ms,List<S>sigs,Literal o){var res=new Vector<M>();var ss=new Vector<>(sigs);var ns=new Vector<>(filter(sigs,s->!any(ms,m->s.m.equals(m.s.m))));
      for(var m:Util.<M>push(filter(ms,x->x.s.m!=null),map(filter(ms,x->x.s.m==null),x->name(x,ns)))){
      var r=m.s.r;
      var taken=filter(ss,s->s.m.equals(m.s.m)&&(r==null||r==s.r));ss.removeAll(taken);
      var match=group(taken,s->s.r);
      if(r==null&&match.size()>1&&or(o.r,or(o.t.erc(),imm)).h().ro()){
        ss.addAll(or(match.remove(mut),list()));
      }var first=true;
      for(var matches:match.size()==0?list(Util.<S>list()):match.values()){
        var mi=first?m:m.body(copy(m.e));first=false;res.add(pair(matches,mi,o));
      }
    }
      group(ss,s->new Key(s.r,s.m)).values().forEach(v->res.add(pair(v,null,o)));return res;
    }
    M pair(List<S>ss,M om,Literal o){
      if(om==null&&ss.size()==1)return new M(ss.get(0));
      var s=om==null?new S(null,null,null,qs(ss.get(0).m.arity),u,null,false,0):om.s;
      if(ss.size()==0){no(s.all().contains(u));
        return om.signature(new S(or(s.r,imm),s.m,or(s.b,list()),s.types,s.t,o.name,om.e==null,s.idx));
      }
      var b=or(s.b,ss.get(0).b);no(any(ss,e->!map(e.b,B::caps).equals(map(b,B::caps))));
      var aligned=map(ss,e->e.subst(b,B.v(e.b),vars(b)));var first=aligned.get(0);
      var types=seq(s.types.size(),i->s.types.get(i)==u?agreement(o,aligned,e->e.types.get(i)):s.types.get(i));
      var res=s.t==u?agreement(o,aligned,S::t):s.t;
      var impl=aligned.stream().filter(e->om==null&&!e.abs&&o.cs.stream().flatMap(c->push(c,from(c.name).cs).stream()).map(c->from(c.name)).noneMatch(d->!d.name.equals(e.o)&&has(d.cs,e.o)&&any(d.ms,m->m.s.o.equals(d.name)&&m.s.m.equals(e.m)&&m.s.r==e.r))).map(S::o).distinct().toList();no(impl.size()>1);
      var out=new S(or(s.r,first.r),first.m,b,types,res,impl.size()==1?impl.get(0):o.name,om==null?impl.size()==0:om.e==null,s.idx);
      return om==null?new M(out):om.signature(out);
    }
    T agreement(Literal lit,List<S>ss,Function<S,T>f){var res=map(ss,f);
      var b=push(lit.b,ss.get(0).b);var first=fill(res.get(0));
      no(!all(res,t->TS.equivalent(b,first,fill(t))));return res.get(0);
    }
    M body(Literal di,M m){
      if(m.e==null)return m;var ei=meet(m.e,m.s.t);cap=deep*size(ei);var g=new IG();g.declare(m);
      g.declare(di.self,di.self(has(di.cs,cf)?imm:m.s.r));var b=push(di.b,m.s.b);
      late=false;var e1=solve(b,g,ei);late=true;return m.body(core(b,solve(b,g,e1),m.e));
    }
    E meet(E e,T t){
      if(!(e instanceof Literal l&&l.t.tv())){var a=ascribe(e,t,null);return a.t(meet(a.t(),t));}
      if(!(empty(l)&&l.cs.size()>0&&meet(l.t,t) instanceof R m&&m.tv()))return e;
      var r=new R(m.r,self(m.c));return r.equals(new R(l.r,l.cs.get(0)))?e:new Literal(null,l.name,list(),list(),l.self,list(),r,true,false);
    }
    T below(R sub,R sup){
      var d=from(sub.c.name);if(d==null||!any(d.cs,c->c.name.equals(sup.c.name)))return null;
      var res=sub.with(meet(sub.r,sup.r),meet(sub.c.types,refine(B.v(d.b),new R(null,new C(sub.c.name,vars(d.b))),sup)));return res.tv()||!sup.tv()?res:sup;
    }
    T meet(T a,T z){
      if(z==u)return a;if(a==u||a.equals(z))return z;
      if(a instanceof R p&&z instanceof R q)return p.c.name.equals(q.c.name)?p.with(meet(p.r,q.r),meet(p.c.types,q.c.types)):or(below(p,q),or(below(q,p),p));
      if(!(a instanceof RX p&&z instanceof RX(var rc2,var q))||!p.x.equals(q))return a;
      return p.rc(meet(p.r,rc2));
    }
    RC meet(RC a,RC b){
      if(a==null||b==null)return or(a,b);return a.h().compareTo(b.h())<0?a.h():b.h();
    }
    T join(T a,T z){
      if(z==u)return a;if(a==u||a.equals(z))return z;
      var cands=list(a,z);for(var top:cands){var res=above(top,cands);if(res!=null)return res;}
      if(all(cands,c->c instanceof R)&&cands.get(0) instanceof R r0){var heads=filter(map(parents(r0.c),C::name),h->all(cands,c->sup((R)c,h) instanceof R s&&s.c.equals(sup(r0,h).c)));
        var minimal=filter(heads,h->!any(heads,h2->!h2.equals(h)&&has(from(h2).cs,h)));if(minimal.size()==1)return above(sup(r0,minimal.get(0)),cands);}
      return u;
    }
    T above(T top,List<T>cands){
      T res=top;for(var c:cands){var up=c instanceof R r&&top instanceof R rt?r.c.name.equals(rt.c.name)?c:sup(r,rt.c.name):Objects.equals(c.v(),top.v())?c:null;if(up==null)return null;
        res=res instanceof R p&&up instanceof R q?any(zip(p.c.types,q.c.types,(x,y)->x.tv()&&y.tv()&&!x.equals(y)),b->b)?null:p.with(lub(p.r,q.r),meet(p.c.types,q.c.types)):res instanceof RX p&&up instanceof RX q?p.rc(lub(p.r,q.r)):meet(res,up);if(res==null)return null;}return res;
    }
    RC lub(RC a,RC b){
      if(a==null||b==null)return or(a,b);var x=a.h();var y=b.h();return x==y||y==iso?x:x==iso?y:read;
    }
    List<T>meet(List<T>a,List<T>z){return zip(a,z,this::meet);}
    E solve(List<B>b,IG g,E e){
      while(true){var s=g.snap();var oe=next(b,g,e);
        if(oe.equals(e)&&s.equals(g.snap()))return e;
        no(oe.t().depth()>cap);e=oe;
      }
    }
    List<E>solve(List<B>b,IG g,List<E>es){return map(es,ei->solve(b,g,ei));}
    E next(List<B>b,IG g,E e){return switch(e){
      case E.X x->{
        var o=g.get(x.name);var a=o;var i=g.indexOf(find(g,f->f.vars.containsKey(x.name)));for(var f:g.subList(i+1,g.size())){no(!B.v(f.b).containsAll(o.ftv().toList()));a=IG.adapt(a,f.r,f.b);}var z=x.t;if(a.equals(z))yield x;
        var t=z==u?null:o==u?z instanceof R(_,var c)?new R(null,c):z
          :o instanceof R p&&z instanceof R q&&p.c.name.equals(q.c.name)?meet(o,z):null;
        if(t!=null)g.get(i).vars.put(x.name,t);yield x.t(meet(a,z));
      }
      case Literal l->{var sp=l.r==null?null:l.self(l.r);if(!l.expanded){if(l.anon&&l.cs.size()==0)inferred.add(l.name.s);
      l=l.t(!l.anon?sp:l.cs.size()==1?new R(l.r,l.cs.get(0)):or(sp,l.t));if(!(l.t instanceof R(_,var c)))yield l;
      var d=l;l=l.anon&&!c.name.equals(l.name)?l.header(push(c,parents(c)),pair(l.ms,map(required(from(c.name)).ms,m->alpha(m,c,d,B.v(b))),l)):expand(l);
    }else if(instance(l)&&cache.containsKey(l.name))yield l;
      var w0=(R)l.t;var ms=new Vector<M>();for(var mi:l.ms)ms.add(mi.e==null?mi:method(b,g,l,sp,w0,mi));var cn=new Vector<Con>();
      for(var m:ms){var h=signature(w0,m.s.m,m.s.r,null);if(h!=null){var mb=B.v(m.s.b);zip(h.ps,erase(m.s.types,mb),(p,a)->cn.add(new Con(p,a,false,true)));cn.add(new Con(h.ret,erase(list(m.s.t),mb).get(0),true,true));}}
      var d=from(w0.c.name);var w=w0.withTs(d==null?map(w0.c.types,this::up):decide(d.b,w0.c.types,cn));
      l=l.header(l.cs,map(ms,m->instantiate(w,m))).t(w);var name=l.name;
      if(!w.tv()||!all(l.ms,m->all(m.s.all(),T::tv))||cache.containsKey(name)&&!instance(l))yield l;
      var bs=cat(methodFree(g,l.ms),supFree(l.cs),w.ftv()).distinct().map(x->B.get(b,x)).toList();var name1=name.arity(bs.size());
      var cap=or(l.r,w.r);if(cap!=null)cap=cap.h();var instance=instance(l);
      var own=w.c.name.equals(name);no(!own&&!w.c.name.visible()&&!w.c.name.pk().equals(p.name));
      var cs=distinct(bs,own?parents(w.c):push(w.c,parents(w.c)));
      l=new Literal(cap,name1,bs,cs,l.self,map(l.ms,mi->mi.o(name,name1)),w,true,true);if(!instance)magic(l,cs);
      if(own)l=l.t(l.self(cap));register(l);var s=sup(w,widen);yield !instance?l:l.t(new R(cap,s!=null&&s.c.types.get(0) instanceof R(_,var c)?c:w.c));
      }
      case Call c->{var e1=solve(b,g,c.e);MS m;
      if(!(e1.t() instanceof R w)||(m=signature(w,c.name,c.r,c.t.erc()))==null)yield c.children(e1,solve(b,g,c.es));
      var n=m.cas.size();var k=m.mb.size();
      var cs=push(new Con(m.ret,c.t,false,true),zip(m.ps,c.es,(p,x)->new Con(p,x.t(),true,!empty(x))));
      var all=decide(push(m.cb,m.mb),push(m.cas,c.written?push(c.y,qs(k)).subList(0,k):qs(k)),cs);
      var es=solve(b,g,zip(c.es,m.ps,(x,p)->meet(x,rename(p,m.v,all))));
      yield new Call(meet(e1,w.withTs(all.subList(0,n))),c.name,m.r,all.subList(n,all.size()),es,meet(c.t,rename(m.ret,m.v,all)),c.written);
      }
    };}
    MS signature(R w,N name,RC favorite,RC hint){
      var d=from(w.c.name);if(d==null)return null;var r=or(w.r==iso?hint:w.r,imm).h();
      var m=find(map(favorite!=null?list(favorite):list(r==iso?imm:r,read,imm,mut),o->find(d.ms,x->x.s.m.equals(name)&&x.s.r==o)),x->x!=null);
      return m==null?null:new MS(m.s.r,push(B.v(d.b),B.v(m.s.b)),d.b,w.c.types,m.s.b,m.s.types,m.s.t);
    }
    boolean instance(Literal l){return l.anon&&all(l.ms,m->m.e==null);}
    boolean empty(E e){return e instanceof Literal l&&instance(l)&&inferred.contains(l.name.s);}
    record Con(T p,T a,boolean in,boolean eq){}
    List<T>decide(List<B>bs,List<T>given,List<Con>cs){var v=B.v(bs);
      Function<Con,List<T>>ref=c->refine(v,c.p,c.a);BinaryOperator<List<T>>join=(a,z)->zip(a,z,this::join);
      var shape=cs.stream().filter(c->c.eq&&c.p instanceof R).map(ref).reduce(given,this::meet);
      var all=cs.stream().filter(c->c.p instanceof R?!c.eq:!c.in).map(ref).reduce(join.apply(shape,cs.stream().filter(c->c.in&&!(c.p instanceof R)).map(ref).reduce(qs(v.size()),join)),this::meet);
      return normalize(bs,map(Stream.of(given,shape,all).reduce((p,z)->zip(p,z,(a,x)->a.tv()?a:x)).get(),this::up));
    }
    M instantiate(R w,M m){var h=signature(w,m.s.m,m.s.r,null);if(h==null)return m;var a=push(w.c.types,vars(m.s.b));
      return m.signature(m.s.types(rename(h.ps,h.v,a),rename(h.ret,h.v,a)));
    }
    T up(T t){if(!(t instanceof R(var r,var c)))return t;var h=sup.getOrDefault(c.name,c);return new R(r,h).withTs(map(h.types,this::up));}
    C self(C c){
      if(!any(from(c.name).ms,m->m.s.abs&&m.s.r!=mut))return c;
      var ss=c.types.stream().flatMap(t->t instanceof R(_,var a)&&parents(a).contains(c)?Stream.of(a):Stream.of()).distinct().toList();
      return ss.size()==1?ss.get(0):c;
    }
    M method(List<B>b,IG g,Literal l,R sp,R w,M m){var bs=l.anon?b:l.b;
      g.push(m.s.r,bs);if(l.anon&&!w.c.name.equals(l.name))sup.put(l.name,w.c);
      g.declare(l.self,sp==null?u:l.self(has(l.cs,cf)?imm:m.s.r));
      g.declare(m);
      var e=solve(push(bs,m.s.b),g,meet(m.e,m.s.t));
      var args=zip(m.v,m.s.types,(x,t)->late?meet(t,g.get(x)):t);
      g.removeLast();return m.signature(m.s.types(args,meet(m.s.t,e.t()))).body(e);
    }
    List<T>erase(List<T>types,List<String>mb){
      return mb.size()==0?types:map(types,t->t instanceof R w?w.withTs(erase(w.c.types,mb)):mb.contains(t.v())?u:t);
    }
    List<T>refine(List<String>v,T t,T a){
      return a==u?qs(v.size()):switch(t){
        case X x->seq(v.size(),i->v.get(i).equals(x.name)?a:u);
        case RX(_,var x)->refine(v,x,switch(a){
          case RX(_,var p)->p;case RI(var p)->p;case R(_,var c)->new R(null,c);default->a;
        });
        case RI(var x)->refine(v,x,a instanceof RI(var p)?p:a);default->propagate(v,(R)t,a);
      };
    }
    R sup(R src,N target){var cs=filter(parents(src.c),ci->ci.name.equals(target));return cs.size()==1?new R(src.r,cs.get(0)):null;}
    List<T>propagate(List<String>v,R r,T a){
      if(!(a instanceof R cc))return qs(v.size());var c=r.c;if(!cc.c.name.equals(c.name)){var up=sup(cc,c.name);
        if(up!=null)return propagate(v,r,up);var down=sup(r,cc.c.name);return down==null?qs(v.size()):propagate(v,down,a);
      }
      var res=zip(c.types,cc.c.types,(t,ti)->t instanceof R rr&&!(ti instanceof R ci&&ci.c.name.equals(rr.c.name))?qs(v.size()):refine(v,t,ti));
      return res.stream().reduce(qs(v.size()),this::meet);
    }
    E ascribe(E arg,T expected,N called){
      if(!(expected instanceof R exp))return arg;
      return switch(arg){
        case Call c->c.children(ascribe(c.e,expected,c.name),c.es);
        case Literal l->!l.anon||l.cs.size()>0||l.t!=u?arg:called==null||from(exp.c.name)!=null&&!any(l.ms,m->called.equals(m.s.m)&&!m.s.all().contains(u))?l.t(new R(exp.r,new C(exp.c.name,qs(exp.c.types.size())))):new Literal(imm,l.name,l.b,l.cs,l.self,l.ms,l.self(imm),true,false);
        default->arg;
      };
    }
    T normalize(T t,Set<RC>al){
      if(al.size()==1)return t.rc(al.iterator().next());
      return t instanceof R(var r,var c)&&(r==null||r==iso&&!al.contains(iso))?new R(al.contains(imm)?null:read,c):t;
    }
    List<T>normalize(List<B>b,List<T>types){
      return zip(types,b,(ti,bi)->ti.v()==null?normalize(ti,bi.caps):ti);
    }
    E core(List<B>ctx,E exp,E orig){return switch(exp){
      case E.X x->x.t(u);
      case Literal e->{var o=(Literal)orig;
      var b=e.anon?cat(e.b.stream(),cat(methodFree(new IG(),e.ms),supFree(e.cs)).map(x->B.get(ctx,x))).distinct().toList():e.b;
      var name=e.name.arity(b.size());var inner=e.anon?push(ctx,b).stream().distinct().toList():b;
      yield new Literal(or(e.r,imm),name,b,map(distinct(inner,push(o.cs,e.cs)),Frontend::normC),e.self,map(e.ms,me->{var mo=me.e==null?me:o.ms.get(me.s.idx);var s=merge(me.s,mo.s);return new M(s,me.v,me.e==null?null:core(push(inner,s.b).stream().distinct().toList(),me.e,mo.e)).o(e.name,name);}),u,e.anon,false);
      }
      case Call e->{var o=(Call)orig;var types=o.written?o.y:e.y;
        yield new Call(core(ctx,e.e,o.e),e.name,or(e.r,imm),seq(types.size(),i->norm(types.get(i).tv()?types.get(i):fillVoid(types.get(i),signature((R)e.e.t(),e.name,e.r,null).mb.get(i)))),zip(e.es,o.es,(a,z)->core(ctx,a,z)),u,false);
      }
    };}
    T fillVoid(T t,B b){return t==u?new R(b.caps.iterator().next(),new C(base("Void",0),list())):t instanceof R w?w.withTs(zip(w.c.types,from(w.c.name).b,this::fillVoid)):t;}
  }
  static List<C>distinct(List<B>b,List<C>cs){var res=new Vector<C>();
    for(var c:cs)if(!any(res,r->TS.equivalent(b,fill(new R(imm,r)),fill(new R(imm,c)))))res.add(c);return res;
  }
  static S merge(S inf,S usr){
    return new S(or(usr.r,or(inf.r,imm)),required(or(usr.m,inf.m)),or(usr.b,or(inf.b,list())),
      zip(usr.types,inf.types,(y,i)->norm(y==u?i:y)),norm(usr.t==u?inf.t:usr.t),required(or(usr.o,inf.o)),usr.abs,usr.idx);
  }
  record G(G tail,String name,T t){
    G add(String name,T t){return new G(this,name,t);}
    G map(UnaryOperator<T>f){return tail==null?this:new G(tail.map(f),name,t==null?null:f.apply(t));}
    T bind(String x){return tail==null?null:name.equals(x)?t:tail.bind(x);}
  }
  record MT(RC r,List<T>types,T t){}
  RC[]reading={imm,iso,readH,iso,mutH,readH},flexy={imm,iso,imm,iso,mutH,readH},hyg={imm,mutH,readH,iso,mutH,readH},strong={imm,iso,imm,iso,iso,imm};
  record TS(Function<N,Literal>decs){
    static void check(List<Literal>tops,Map<N,Literal>other){var map=new HashMap<N,Literal>();
      tops.forEach(t->collect(t,map));var sys=new TS(n->from(n,map::get,other));tops.forEach(l->sys.check(new G(null,null,null),l,has(l.cs,cf)?imm:l.r));
    }
    static void collect(E e,HashMap<N,Literal>map){if(e instanceof Literal l)map.put(l.name,l);e.children().forEach(c->collect(c,map));}
    boolean kinded(List<B>b,T t,Set<RC>al){
      return al.containsAll(kinds(b,t))&&(!(t instanceof R(_,var c))||!zip(c.types,decs.apply(c.name).b,(ti,p)->kinded(b,ti,p.caps)).contains(false));
    }
    void kind(List<B>b,T t,Set<RC>al){no(!kinded(b,t,al));}
    static Set<RC>kinds(List<B>b,T t){return switch(t){
      case R(var r,_)->caps(or(r,read));case RX(var r,_)->caps(r);
      case RI(var x)->EnumSet.copyOf(map(kinds(b,x),RC::ri));default->B.get(b,t.v()).caps;
    };}
    boolean sub(List<B>b,T a,T z){return a.equals(z)
      ||z instanceof RI(var q)&&q.equals(a)&&kinded(b,a,plain)
      ||equivalent(b,a.rc(mut),z.rc(mut))&&all(kinds(b,a),r1->all(kinds(b,z),r1::sub))
      ||a instanceof R(var rc1,var c1)&&decs.apply(c1.name) instanceof Literal d&&any(d.cs,ci->sub(b,rename(new R(rc1,ci),B.v(d.b),c1.types),z));
    }
    List<T>type(List<B>b,G g,E e,List<T>rs){return switch(e){
      case E.X x->reqs(b,required(g.bind(x.name)),rs);
      case Literal l->{
      var gf=g.map(t->has(l.cs,cf)||!t.ftv().allMatch(B.v(l.b)::contains)?null:t);var r=(l.r.ro()&&!any(l.ms,m->m.s.abs&&m.s.r==mut)||l.r==mut)&&cf(l.b,gf,l)?iso:l.r;
      no(any(l.ms,m->(m.s.abs||m.e!=null&&!inst(l))&&m.s.abs==(m.s.r!=mut||!r.ro())));
      var t=l.self(r);kind(b,t,allRC);check(gf.map(x->!kinded(l.b,x,plain)||r.ii()&&!kinded(l.b,x,ii)?null:x),l,has(l.cs,cf)?imm:l.r==iso?mut:l.r);
      yield reqs(b,t,rs);
      }
      case Call c->{
      if(!(type(b,g,c.e,list()).get(0) instanceof R h))throw new Fail();var d=decs.apply(h.c.name);
      var s=canonical(d,c.name,c.r);
      no(s.b.size()!=c.y.size()||zip(c.y,s.b,(t,p)->kinded(b,t,p.caps)).contains(false));
      var v=B.v(push(d.b,s.b));var ts0=push(h.c.types,c.y);
      var base=new MT(s.r,rename(s.types,v,ts0),rename(s.t,v,ts0));
      var app=cat(Stream.of(base,apply(b,base,flexy,flexy,-1,flexy),apply(b,base,strong,strong,-1,strong),apply(b,base,reading,reading,-1,hyg),apply(b,base,hyg,flexy,-1,hyg)),
        range(base.types.size()).mapToObj(i->apply(b,base,flexy,flexy,i,hyg))).distinct().filter(m->h.r.sub(m.r)).toList();
      var possible=new Vector<>(app);range(c.es.size()).forEach(i->{
        var reqs=app.stream().map(m->m.types.get(i)).distinct().toList();var got=type(b,g,c.es.get(i),reqs);
        possible.removeIf(m->got.get(reqs.indexOf(m.types.get(i)))==null);
      });
      no(possible.size()==0);yield rs.size()==0?list(best(b,possible)):map(rs,req->best(b,filter(possible,m->sub(b,m.t,req))));
      }
    };}
    static boolean inst(Literal l){return l.self.equals("this")||has(l.cs,cf);}
    static long count(String x,E e,boolean active){
      return e instanceof E.X v?v.name.equals(x)?1:0:active&&e instanceof Literal?0:e.children().mapToLong(c->count(x,c,active)).sum();
    }
    List<T>reqs(List<B>b,T got,List<T>rs){
      return rs.isEmpty()?list(got):map(rs,r->sub(b,got,r)?got:null);
    }
    boolean cf(List<B>b,G g,E e){
      return e instanceof E.X x?g.bind(x.name)==null||all(kinds(b,g.bind(x.name)),RC::ii):e.children().allMatch(c->cf(b,g,c));
    }
    void check(G g,Literal l,RC self){
      if(has(l.cs,identity)){var m=l.ms.get(0);no(!switch(m.e){
        case null->true;
        case E.X(var name,_)->name.equals(m.v.get(0));
        case Call c->c.e instanceof E.X(var recv,_)&&recv.equals(m.v.get(0))&&c.name.equals(new N(".as",1))
          &&m.s.types.get(0) instanceof R(_,var cc)&&has(decs.apply(cc.name).cs,container);
        default->false;
      });}
      for(var parent:l.cs){kind(l.b,new R(imm,parent),allRC);var sup=decs.apply(parent.name);no(!inst(sup));for(var m:filter(sup.ms,x->x.s.o.equals(sup.name))){
        var c=canonical(l,m.s.m,m.s.r);var s=m.s.subst(c.b,B.v(push(m.s.b,sup.b)),push(vars(c.b),parent.types));var ctx=push(l.b,c.b);
        no(zip(push(c.types,s.t),push(s.types,c.t),(p,q)->!((p instanceof RI)==(q instanceof RI)&&p.erc()==q.erc()||equivalent(ctx,p,q))||!sub(ctx,q,p)).contains(true));
      }}
      var g1=g.add(l.self,l.self(self));for(var m:l.ms){var g2=g1.map(t->IG.adapt(t,m.s.r,l.b));
        var bs=push(l.b,m.s.b);m.s.all().forEach(t->kind(bs,t,allRC));if(m.e==null)continue;
        for(int i=0;i<m.v.size();i++){var x=m.v.get(i);var ti=m.s.types.get(i);g2=g2.add(x,ti);no(!kinded(bs,ti,caps(mut,read,mutH,readH,imm))&&count(x,m.e,true)>0&&count(x,m.e,false)!=1);}
        no(type(bs,g2,m.e,list(m.s.t)).get(0)==null);
      }
    }
    S canonical(Literal l,N name,RC r){return required(find(l.ms,m->m.s.m.equals(name)&&m.s.r==r)).s;}
    static boolean equivalent(List<B>b,T p,T q){
      return p.equals(q)||(p instanceof R(var aRc,var aC)&&q instanceof R(var bRc,var bC)?aRc==bRc&&aC.name.equals(bC.name)&&!zip(aC.types,bC.types,(s,t)->equivalent(b,s,t)).contains(false)
        :p.rc(imm) instanceof RX(_,var x)&&p.rc(imm).equals(q.rc(imm))&&B.get(b,x.name).caps.size()==1&&kinds(b,p).equals(kinds(b,q)));
    }
    T best(List<B>b,List<MT>ms){var types=map(ms,MT::t);return find(types,p->!any(types,q->!q.equals(p)&&sub(b,q,p)));}
    MT apply(List<B>d,MT m,RC[]receiver,RC[]args,int at,RC[]result){
      return new MT(receiver[m.r.ordinal()],seq(m.types.size(),j->adapt(d,m.types.get(j),j==at?hyg:args,(p,q)->q.sub(p))),adapt(d,m.t,result,RC::sub));
    }
    T adapt(List<B>d,T t,RC[]mode,BiPredicate<RC,RC>le){
      if(t.erc()!=null)return t.rc(mode[t.erc().ordinal()]);var x=t.v();
      var caps=map(B.get(d,x).caps,r->t instanceof RI?r.ri():r);if(all(caps,r->mode[r.ordinal()]==r))return t;
      var up=filter(allRC,p->all(caps,c->le.test(mode[c.ordinal()],p)));return new RX(find(up,p->all(up,o->le.test(p,o))),new X(x));
    }
  }
}
