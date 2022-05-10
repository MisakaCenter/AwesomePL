1 我今天介绍的是一个根据数据类型等价性来自动修复证明的工具，他是以一个集成在coq的插件形式Pumpkin Pi来实现的。



4 因为coq 的交互是用户把program、proof等写到coq中，然后他帮你检查正确性。



5 但是当你做了一些change之后，往往这个coq就不会认为你现在的proof是对的。



6 有理由相信，去修改一个program往往要比第一次来证明要简单，所以本篇文章就是作者在改变数据类型的情况下，想要自动修复证明。



7 原本coq的workflow是：用户在coq high-level构建的是tactic（像induction这种），在证明过程中一系列tactic就是proof script。

为了检查proof script的正确性，coq会把他编译到low-level，proof term，然后检查这个term是否是我们预期的类型。

本文的证明修复工作是在low-level的proof term上实现的，然后会把修改后的term再构建成hlgh-level的proof scripts。



8 总体来讲，punpkin pi的workflow是这样的。

用户手动（工程师指定，可以在任意equivalence之间transformation，都不用search procedure）或自动（自动配置有四个search步骤）对类型的等价性做配置，这个configure就是告诉proof term如何从旧类型把函数、证明转换到新类型那种格式。并且不要破坏definitional equality。

然后根据这个configuration，旧的proof term会transform 为新的proof term。

最后再将proof term 反编译decompile为新的proof script。



10 介绍一个简单的例子，这是把list这个datatype的两个构造子交换了。左边是原来的，右边是交换过的新的。那么对于coq标准库里这个lemma：原来的proof script靠对x和y做induction，最后通过pumpkin pi得到的修复过的证明是右边的样子。（它里面的其他依赖，rev，++，app-assoc，app-nil-r都会自动更新。）不仅交换了行，还交换了参数。



12 刚才的例子是交换了构造子，但是本文能实现的不止是这些，只要满足type A 和 B 之间有equivalence，那么就能修复用B替代A之后的函数和证明。

这个equivalence在AB之间可以用这个符号表示。下面这个图是在刚刚那个交换构造子的例子的延伸，这就是pumpkin pi发现并且可以自动证明的type equivalence。swap函数是把旧的list转换为新的list。swap‘函数是把新的转换为旧的。那么section就是，retraction、就是。

所以本质上就是一组函数在两种或多种type之间的循环。

之前的search步骤就是给了新旧type之后，会寻找并且自动证明这种这种描述改变的等价性。



13 规定以下两种改变是等价：

+ 分解构造子

本来在类型I中，ab是两个不同的构造子

现在用同一个构造子makej，但是用bool来表示不同的两个

所以只要配置出I中那个构造子map到true，那个映射到false。就可以用J代替I

+ 加一个dependent的索引。

将一个列表改为一个具有长度索引的向量，这样可以确保在编译的时候这个list的长度是不变的。



14 有了equivalence之后，pumpkin pi的目标是transport，也就是假如A和B等价，那么transport要做的就是对原来的term t，构造出一个新的t‘。如果t是个函数的话，那么t'和t表达同一个意思。如果t是个证明的话，那么t'和t用同一种方法证明同一个定理。那么t和t'是equal up to transport的话就可以写作这种形式。



16 因为工作在term层，所以核心是要像之前说的，有个可以确保等价性的configuration，然后根据这个再做transform生成新的term。

在介绍之前先做一些规定。

+ CoC（ the Calculus of Constructions） 是lambda cakculus的变种，
+ polymorphism： (types that depend on types) 
+ dependent types： (types that depend on terms)
+ CICw extends CoC with inductive types。
+ inductive type：是构造子constructor和 eliminators (like the induction principle for list）定义的

本文所说的terms是CICw中的（Calculus of Inductive Constructions）

下面这个是CICw的语法。那么这个term的构成从左到右 依次是variables, sorts, dependent types（依赖于term的类型）, functions, 两个term间的application, inductive types, inductive constructors, and primitive eliminators.



17 下面来介绍configuration

每个configuration都对应于一对等价的类型。

configuration主要帮助一会要介绍的transformation实现两个目标：

（1）在跨类型等价性传输时保持等价性（2）生成新 terms

这个configuration是主要包括四个元素：((DepConstr, DepElim), (Eta, Iota))

dependent constructors and eliminators

前一对 ：确定如何对constructors and eliminators做转换且不失等价性, 是为了实现目标1

后一对 ：是为了实现目标2生成新term

 

18 目标1:  保持等价性

本篇文章规定的两个类型不一定有相同数量的构造子，甚至可能都不是有inductive结构，但是通过处理后生成的depcon和elim参数等等肯定是相同数量的

对之前那个交换构造子的例子，左边是原来的，右边是新的。configuration的constr和elim都交换了。

对于有长度的vector这个例子，原来是list，也有configuration。

这个打包的把索引也打包成存在的了

depelimi消除了投影（pi-l和r是s的左右的投影）

 

19 目标2:  生成新term

CICw区分了两种equality：definitional equality（by reduction） 和propositional equality（by proof）

(1) 如果type T 的2 个terms t t’，会归约到同一个标准型。

(2) 要证明才能是一样的term

Eta和Iota： 描述了如何转换等价性. 定义了η-expansion and ι-reduction of A and B

η-expansion： 这是一个对term的扩展，通过把constructor apply 到 eliminator 上。保证命题的等价性。

ι-reduction ：对一个constructor的elimination进行还原。

每个Iota描述并且证明了depelim上的iota-reduction

 

20 例子4:  

一元自然数 nat

二进制自然数 N（0:N0，Npos：positive的（1:xH、左移加1 (xI) 、左移加0 (xO)））

nat和N是等价的，但是不同的inductive structure

definitional equalties over nat -> propositional equalities over N.

已经定义了depconstr和depelim确保equivalence。为了移植证明，需要把nat的definitional  转换到N的 propositional 。

nat：

ι-reduction是definitional，hold by reflexivity。Iota也是by the proof by reflexivity



21 N：

ι-reduction是propositional，不是hold by reflexivity。Iota是by propositional equality 

这样通过将nat的Iota替换为N的Iota，那么nat的defonitional变为N的 propositional equalities。这样 ，DepElim对nat和N的行为就相同了。因为transformation要求A和B的DeqElim有相同结构。

所以如果A和B的inductive structure相同，那么ι is definitional for A, it will be possible to choose DepElim with definitional ι for B。如果A和B的inductive structure结构不同（像nat和N一样），那么definitional ι over one would become propositional ι over the other.

 

22 在有了configuration之后，就进入transformation了。这个图就是在有了configuration的情况下，在AB的转换terms。有appli，var，等等。一些基本的结构

 原始coq的term不会显示用这些configuration，本文是 通过unification 统一化来在做转换之前得到这种形式的proof term，然后再run transformation（会根据configuration把proof跨类型转换。）

 

23 Unification.

对于之前那个交换构造子的例子， 

Pumpkin Pi 先统一configuration。用A统一 Old.list T, 用DepConstr and DepElim统一Constr and Elim。 

在做了统一之后，用B代替A, 得到转换后的term。

最后再还原到coq的交换过构造子term形式。 

 

24  现在是可以做转换了，可以有多个equivalence对应于一个变化，其中只有一些是有用的。

可能有很多configuration对应一个equivalence，其中有一些事能产生有用有效的terms

比如说 f是函数：使用DepElim（A）和DepConstr（B）, and let g be similar。

下图，指定了configuration的正确性标准。这些准则将 DepConstr, DepElim, Eta, and Iota、以一种能保持等价的方式联系起来。

  

25 Equivalence.

图的左侧。DepConstr and DepElim必须equivalence（对于f和g必须支持section

and retraction）。

(constr_ok)：A和B上的DepConstr必须equal up to transport across that equivalence

elim_ok：DepElim也要等价

constr_ok 和 elim_ok 对于subterm也能保持等价性。这样的transformation就可以不用应用f和g，直在A和B直接移植term就行了。

Equality

图的右侧。为了保证equality的一致性，Eta 和Iota 必须证明 η 和 ι。

elim_eta ：Eta必须有相同的definitional behavior 像 dependent eliminator一样 ，

iota_ok：Iota必须根据dependent eliminator证明并重写简化

Correctness.

有了这些configuration的正确性标准，得到了完备性completeness结果，每个equivalence都引出（induce）一个 configuration。并且（soundness）结果：每个configuration 会引出induces 一个equivalence。

 

27  Transform 生成 a proof term, 用户通常用proof scripts.

所以要把 terms 反编译成proof scripts。

反编译两个步骤： 

第一个（1）：把proof terms反编译为使用预定义tactic集的证明脚本scripts。

第二个（2）：通过简化参数、替换tacticals和使用custom tactics和decision procedures等提示来改进tactic。    

第一步  

实现一个mini decompiler，使用CICw 定义的terms和mini版本的Ltac（Qtac）。

Qtac的语法：intro，rewrite等等

Qtac的语义：    默认使用apply，不然的话反编译器都会递归，分解，直到只有基本情况成立。

下面这个图就是当初交换构造子的例子，这个script已经是用户能修改维护理解的了。  

 

32 是8种情况的研究例子

 

33 本文结合了等价性的搜索过程search procedures for equivalences、一个证明项转换 a proof

term transformation和一个策略反编译器的证明项a proof term to tactic decompiler来构建南瓜Pi，一个用于数据类型变化的证明修复工具 a proof repair tool for changes in datatypes。



 

​                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             