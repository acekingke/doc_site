# Effecicent Computation of LALR(1) look-Ahead Sets 

Frank DeREMER and Thomas Pennello

## 1 . 引论

自从DeRemer发明了LALR(1) 语法来，LALR语法分析与解析技术作为语言转写系统或额编译器的编译器一个组件，越来越流行。但是DrRemer并没有描述如何计算所需的前看符号集，相反，LaLonde首先阐述了一个算法【20】自从那开始，Lalonde的算法开始有Aderson 等人发表【6，pp. 21-22】,并且展示了自己的算法【6，p.21】，Aho与Ullman【3，P.238】则发表了用在YACC【16】的算法。Kristensen与Madsen【19】则改进了LaLonde的算法，将其结果拓展到LALR(k)。

还有很多其他的人打算设计这种算法，常常结果是实现了一个LALR(1)算法的特定的子集，我们给它们起一个外号为“不完全（NOT quite）” LALR（1），或称NQLALR(1) [7,11,23,25]，随后，Watt尝试修复他的原始方法【24】，如Chaney对Deramer方法的改造一样【5】它们之后的尝试几乎没有正确的，虽然他们比NQLALR方法更复杂，能适应更多情况

除了Kristensen和Madsen【19 Sec.6.2】开发的算法已经接近NQLALR(1)的效率外，没有一种LALR(1)是正确的。之后我们会描述过于简化的简单、高效算法并不完全正确。本文的目的是利用问题的核心结构提供一个高效的算法。

### 1.1 前言

当某语法不少LR(0)语法，则说明有一个或者多个LR(0)解析器状态是“不一致的”（inconsitent）, 要么有`read-reduce`冲突，要么有`reduce-reduce`冲突，后者两者都有。前一种情况，解析器不知道如何决定应该是移进还是应该归约。后一种情况，则是解析器不知道选取那个规则进行归约。向前查看输入串（input）中第一个符号就可能解决冲突，DeRemer定一种LALR(1)语法：在“不一致”状态q可以使用`look ahead set`(向前看符号集)来解决冲突，达到正确、确定的或称`一致性的`的解析器。

更精确地、每个“不一致性”状态q，和q内可能的归约$A\to \omega$, 将$A\to \omega$的向前看符号集记作$LA(q, A \to \omega)$. 当解析器处于q并且输入串头一个符号是$LA(q, A \to \omega)$里的符号，$\omega$ 就需要归约成为A。当然，q种所有的`look ahead set` 必须相互不相交（两两交集为$\empty$）,并且也不能包含q要从input读入（或称移进）的终结符号。

Watt【24】定义了$LA(q, A \to \omega)$ 为$\{t \in T| S \implies{^+} \alpha Atz \text{ and } \alpha \omega  \text{ acecess q } \}$ ,其中，T为语法G中的终结符集，$\alpha\omega$ `accesses q` 读作$\alpha\omega$ 到达状态q，非常直观地，堆栈顶符号串为$\alpha\omega$时，此时input中以某终结符t开始，在最右句型中，t会尾随（follow）$\alpha A$, 此时用$A\to \omega$进行归约就非常恰当。我们的目的是研究该定义的潜在结构，并展示如何高效计算LA。

该问题可以解耦为四个独立计算，以逆序方式描述是：LA从非终结符转移（nonterminal transistion）的Follow集计算，Follow集从非终结符中的Read集计算，而Read集从“Direct Read”中计算。而Direct Read直接从LR(0)解析器计算出来。

与follow集相关的定义是非终结符转移的**include** 关系，与read集相关的定义是**reads**， 然后通过图遍历算法找到“强连通分量”（strong connected component ，简称SCC），随着搜索有向图推导出**reads**关系，并合并合适的集合。如果发现非平凡的SCC（平凡SCC仅仅含一个节点），问题所示的语法就不是LR(k)算法，k为任意自然数。接着Read集合作为Follow集合的初始值，应用**include**关系，再次，如果发现非平凡SCC，并且没有非空的read集合，（我们猜测）语法也不是LR(k)语法，其中k为任意自然数。在以上各种情况下，LALR(1)的look-ahead集合则是Follow集合简单合并。

## 术语

字典（vocabulary）是符号集合，V* 表示V中生成的所有符号串(string)（包含空串），V+表示$V^{*} - \{\epsilon\}$, $\epsilon$ 表示空串(empty string)。$\alpha$的长度用$|\alpha|$表示。

非空字符串$\alpha$ 的第一个符号记作 First $\alpha$ , 其他的符号组成的串记作 Rest $\alpha$ , 最后一个符号记作 Last $\alpha$

如果R是一个关系，$R^{*}$ 表示自反、传递的R闭包（closure），  $R^{+}$ 表示传递闭包。

$X =_s  F(X)$ 表示X是满足$X= F(X)$的最小集。

$\cup \{S_1 \ldots S_n \}$其中$S_i$是集合，表示$S_1 \cup \cdots \cup S_n$ 

### 2.1 CFG

上下文无关文法CFG (context free grammar)是一个四元祖$G=<T, N, S, P>$ 其中T是终结符有限集合，N是非终结符有限集合，且$T \cap N = \empty$   ， $S \in N$ ， S为开始符号。 P 也是一个有限集合，是$ N \times V^*$的子集。其中$V=T \cup N$， 其中$(A, \omega )$ 是产生式，记作$A \rightarrow \omega$ , A 称为左部，$\omega$ 称为右部。此外，我们还要额外的产生式 $ S \rightarrow S^{'}\bot $ 新增非终结符${S^{'} \in N}$, 以及终结符${\bot \in T}$ , 并且S 与$\bot$ 不会再任何产生式右部出现（注:增广文法）。

本文常用惯例表示如下：

S, A, B, C ... $\in$ N

X $\in$ V

t,a, b, c... $\in$ T

... x,y,z $\in T^{*}$ 

$\alpha,\beta, \gamma \in V^{*}$

关系$\implies{_r}$ 读作“直接（右）生成”， 定义域为$V^{*}$ ,所以有$\alpha Ay \implies_{r} \alpha\omega y$ 其中 $\alpha \in V^{*}$, $y \in T^{*} $ 且$A \rightarrow \omega \in P$ 

下表r在自此均丢弃，$\implies$ 默认是最右生成。而 $\implies^{*} 与 \implies^{+}$都读作“生成”（produce）

可空非终结符（nullable nonterminal）表示可以生成$\epsilon$ 的非终结符

如果 $S \implies^{*}  \alpha$ 则$\alpha$ 称为句型(sentential form)，如果$\alpha \in T^{*}$ ,则$\alpha$ 称为句子(sentence)

语言L(G) 表示由语法G生成的句子集合。即$\{x \in T ^{*}|S \implies^{+} x\}$ 这里假设所有的语法都可以被归约(reduce) 即所有$S \implies ^{+} \alpha A \beta$ 所有$A \in N$  都有 $A \implies ^{*} y$ , 而某些$\alpha , \beta \in V^{*}$ 且 $y \in T^{*}$

设G是一个CFG，并且$k \geq 0 $, G 是一个LR(k),当且仅当  $S \implies^{*} \gamma \implies \alpha \omega y' $ 蕴含 $\forall \alpha, \gamma \in V^{*} $, 且$ y, y' \in T^{*}$ 均有 $First_k(y') = First_k(y)$ 其中$First_k(y)$ 表示y的长度为k的前缀，如果$|y| < k$ , 那么$First_k(y)$ 即y本身

### 2.2 LR解析器

现在介绍LR的标准形式，任意前看一个符号的解析器，如SLR(1), LALR(1), LR(1). 虽然前看多个符号的解析器也容易生成，但是与本文无关。下面给出一些表格形式的“LR自动机”以及通用LR解析算法来解释这些表格，就得到一个LR解析器。

一些特殊的状态、转换函数和look-ahead集合由本讨论中的语法与构造技术来确定。例如，LALR(1)产生一个“LALR(1) automation(自动机)“

CFG语法 $G= <T, N, S, P>$的LR自动机是一个六元组$LRA(G)=<X,V,P,Start, Next, Reduce>$， 其中K是状态的有限集，V和P与G中的定义相同。$Start \in K$ 是开始状态， $Next : K \times V \rightarrow K$称为转移函数， $Reduce:K \times T \rightarrow 2^{P}$ 称为归约函数。Next也可能是偏函数（Partional function） ，在LR自动机中，不一致或非确定性是允许的，但是在LALR情况下（段3）已经排除了这种情况。一个*转移* 是$K \times V$的成员， 如果是$K \times T$ 的成员则是终结符转移，如果是$K \times N$ 的成员，则是非终结符转移， 转移(q, X) 表示

$$
q \xrightarrow X p​
$$

其中p=Next(q, X)  , 也可以这样表示
$$
q \xrightarrow X
$$
此时p状态无关紧要。我们定义”到达符号“ Accessing_symbol p = X , 除了开始状态无Accessing_symbol外，其他的状态都有Accessing_symbol

在本文中的图表，LR自动机有状态图表示，状态图有状态，状态由转移（transistion）链接，每个状态列出来可能用到产生式列表用以归约。

路径（**path**）H 是一个状态序列$q_0 \dots , q_n$ 有
$$
q_0 \xrightarrow {X_1} q_1 - \cdots \xrightarrow {X_n} q_n
$$
我们说$ H\text{ spell } \alpha=X_1\dots X_n$ 并且定义$\text{ Spelling } H = \alpha $ 以及 $\text{ Top } H = q_n$ , H 记作$q_0 - \overset{\alpha}{\cdots} \rightarrow q_n$ , 读作" $q_0 \text{ goes to } q_n \text{under } \alpha$ " (q0在$\alpha$ 下跳到qn) ， 也可以记作 给定自动机或者状态图，H为$[q_0:\alpha]$ ， 如果$\text{ Top } [q:\alpha] = q'$ ,则 $[q:\alpha]$  与$[q':\alpha']$ 连接记作$[q: \alpha][q': \alpha']$ 并记作$[q:\alpha \alpha']$ 其中$[Start: \alpha]$ 可以简记为$[\alpha]$ ,      而[ ] 表示start状态

一个构型(configuration)是$K^+ \times T^+$ 的成员，第一部分称为状态栈（state stack）第二部分称为输入串（input），构型上的关系$\vdash$读作“直接移动到” （directly move to），包含$\vdash_{read}$ 和$\vdash_{A \rightarrow \omega} \forall A \rightarrow \omega \in P$ , $\vdash_{read}$ 读作“reads to”： 如果$\text{ Next } ( \text{ Top } [q : \alpha], t) $ 已经定义，则可以表示为 $ [q : \alpha]tz \vdash_{read} [q :\alpha t]z $ ,  而$\vdash_{A \rightarrow \omega} $读作 “reduce $ \omega $ to A in Moving to" (将 $\omega$归约到A， 并将状态移动到) ：当$A \rightarrow \omega \in \text{ Reduce }(\text{ Top } [q : \alpha \omega], t)$ $[q: \alpha \omega]tz \vdash_{A \rightarrow \omega} [q: \alpha A]tz$ (如果$[q: \alpha A]$ 是一个路径，但是在这里的LR自动机需要考虑额外的约束条件)  $\vdash^{*}$与$\vdash^{+}$读作“move to”(移动到) ，语言L(LRA(G)) 由LRA(G)解析，一定能识别L(G)语言，并且语言是$\{z \in T^* | [] z \vdash^+ [S'] \bot \}$

> 注：这里的t是终结符，A是非终结符，z是终结符组成的串，而希腊字母表示是V* 中的串

三元组$(A, \alpha ,  \beta) \in N \times V^* \times V^*$ 称为项(item), 如果$A \rightarrow \alpha \beta$是一个产生式，item可以写作  $A \rightarrow \alpha \cdot \beta$， 如果$\beta= \epsilon $ ,则为最终项（final item），项目的集合称为一个（解析）表。CFG语法G的LR(0)解析表PT(G) 是：
$$
PT(G) =_s \{ \text{Closure} \{S \rightarrow \cdot S' \bot \}\} \cup \{\text{ Closure }IS |IS \in \text{ Successors } IS' \in PT(G)\}
$$
其中
$$
\text{Closure }IS = IS \cup \{ A \rightarrow \cdot \omega | B \rightarrow \alpha \cdot A \beta \text{ and } A \rightarrow \in P\} \\
\text{ Successors } IS = \{ Nucleus(IS, X)| X \in V\} \\
Nucleus(IS, X) = \{A \rightarrow \alpha X \cdot \beta|A \rightarrow \alpha \cdot X \beta \in IS\}
$$


一个上下文无关文法CFG G， LR(0) 自动机是一个LR自动机LRA(G)， 存在一个双射函数$F: K \rightarrow PT(G) - \{ \empty \}$

其中：
$$
Start = F^{-1} (Closure \{S \rightarrow \cdot S' \bot \})
$$
并且
$$
Next(q, X) = F^{-1}\{Closure(Nucleus(\text{F } q, X))\} \\
Reduce(q, t) = \{A \rightarrow \omega \cdot \in \text{F }q \}.
$$
F是表（除开$\empty$ ,即“trap table”，陷入表）与状态之间的简单一一对应函数，因此解析表与解析器之间是同构（isomorhism）的。因此，此后我们省略F与F‘，依据上下文来确定q是状态还是解析表。自动机的LR(0)样式（LR(0)-ness）明显之处在于Reduce(q, t)定义不依赖于t。自此之后，我们常常用解析器而不是自动机。

众所周知，LR(0)自动机A是语法G的正确解析器，即$L(A) = L(G)$ ;然而，一般来说，它们是不确定的，因为总存在“不一致”（inconsistent）的状态。一个状态q不一致，当且仅当Next(q, t) 已定义，且$Reduce(q, t) \neq \empty$ (read-reduce 冲突)， 或者$|Reduce(q, t) | > 1 $ , 即（reduce-reduce冲突）,或者是两者兼有之.

有一个简便的记法表示一个特定系列的移动（包含read与reduce）非常有用：
$$
[\alpha | ]yz \vdash^*[\alpha|\beta]z \iff (\text{Top }[\alpha], yz) \vdash^*([\text{Top }[\alpha]:\beta],z).
$$

> 注：$y \in T^*, \beta \in V^*$

这个记号表示的是，解析器读取y串，然后归约到$\beta$ 串，可能包含先于y之前进行空串归约($\epsilon$归约) 。中间的竖线是必要的，因为$[\alpha]yz \vdash^*[\alpha \beta]z$ 并不必定推导出$y$会被归约为$\beta$ ,举个例子，考虑
$$
[\gamma A]txz \vdash_{read} [\gamma At]xz 
 \vdash_{A \rightarrow At} [\gamma A]xz\vdash^*[\gamma A \beta]z
$$
其中$tx$ 不会被归约为$\beta$ (这里$y = tx 且\alpha=\gamma A$)

### 2.3 图

一个有向图（directed graph 或称 digraph）是一个pair（V'，E）其中V' 是一个顶点集合，E是$V' \times V'$ 的子集，每个成员称为边（edge），在本文中V'始终是指有限集合。

