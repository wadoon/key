<TeXmacs|1.0.7.11>

<style|article>

<\body>
  <doc-data|<doc-title|Symbolic execution based test case
  generation>|<doc-author-data|<author-name|Christopher
  Svanefalk>|<\author-address>
    \;
  </author-address>|<\author-address>
    B.Sc. Thesis.
  </author-address>|<\author-address>
    University of Gothenburg, 2012

    \;
  </author-address>>>

  <\abstract>
    Software testing is a verification technique frequently used in software
    engineering, aiding both the development of the system itself, as well as
    subsequent quality assurance and maintenance. It suffers, however, from
    the drawback that writing test cases is a tedious and resource heavy
    process. This work outlines an automatic approach to test case generation
    based on symbolic execution, which aims to address this problem by
    automating the creation of robust test suites. In particular, it details
    strategies for instantiating concrete heap states from symbolic metadata.
    The application of these principles are then demonstrated in the
    KeYTestGen2 system.\ 
  </abstract>

  \;

  <new-page*>

  \;

  \;

  \;

  \;

  \;

  \;

  <\with|par-first|0fn>
    <\with|par-mode|left>
      <\with|par-left|10cm>
        <\with|par-left|5cm>
          <\with|par-left|2cm>
            <\with|par-right|2cm>
              <strong|Acknowledgement>

              \;

              This work has been made possible through the tireless support
              of the KeY community. I especially thank Dr. Reiner Hähnle, Dr.
              Richard Bubel, and Martin Hentschel, Mr.Sc. and their
              colleagues at the Darmstadt University of Technology, for
              letting me stay and work with them leading up to the 2012 KeY
              Symposium. My deepest thanks also to Dr. Wolfgang Ahrendt,
              Gabriele Paganelli, Mr.Sc. and the Software Engineering using
              Formal Methods group at Chalmers, for inviting me to join them
              in their work.
            </with>
          </with>
        </with>
      </with>
    </with>
  </with>

  <new-page*>

  <\table-of-contents|toc>
    <vspace*|1fn><with|font-series|bold|math-font-series|bold|1<space|2spc>Introduction>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-1><vspace|0.5fn>

    <with|par-left|1.5fn|1.1<space|2spc>The pursuit of correctness
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-2>>

    <with|par-left|1.5fn|1.2<space|2spc>Scope of this work
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-3>>

    <with|par-left|1.5fn|1.3<space|2spc>Organization
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-4>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|2<space|2spc>Fundamental
    concepts> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-5><vspace|0.5fn>

    <with|par-left|1.5fn|2.1<space|2spc>A formal look at correctness
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-6>>

    <with|par-left|3fn|2.1.1<space|2spc>The Java Modelling Language
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-7>>

    <with|par-left|1.5fn|2.2<space|2spc>Software verification and
    verification methods <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-8>>

    <with|par-left|3fn|2.2.1<space|2spc>The verification ecosystem
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-9>>

    <with|par-left|3fn|2.2.2<space|2spc>The formal methods
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-10>>

    <with|par-left|3fn|2.2.3<space|2spc>Software testing
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-11>>

    <with|par-left|1.5fn|2.3<space|2spc>Unit testing
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-12>>

    <with|par-left|1.5fn|2.4<space|2spc>Test cases and test suites
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-13>>

    <with|par-left|1.5fn|2.5<space|2spc>Automating testing
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-14>>

    <with|par-left|1.5fn|2.6<space|2spc>Automating test case generation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-15>>

    <with|par-left|3fn|2.6.1<space|2spc>Black box test generation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-16>>

    <with|par-left|3fn|2.6.2<space|2spc>White box test generation
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-17>>

    <with|par-left|3fn|2.6.3<space|2spc>White box vs black box
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-18>>

    <with|par-left|1.5fn|2.7<space|2spc>A metric for test quality: code
    coverage <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-19>>

    <with|par-left|3fn|2.7.1<space|2spc>Logic coverage
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-20>>

    <with|par-left|3fn|2.7.2<space|2spc>Graph coverage
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-21>>

    <with|par-left|1.5fn|2.8<space|2spc>Symbolic execution
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-22>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|3<space|2spc>Background>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-23><vspace|0.5fn>

    <with|par-left|1.5fn|3.1<space|2spc>Early work - KeY and the Verification
    Based Test Generator <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-24>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|4<space|2spc>The
    KeY system> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-25><vspace|0.5fn>

    <with|par-left|1.5fn|4.1<space|2spc>KeY - an overview
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-26>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|5<space|2spc>KeYTestGen2>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-27><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|6<space|2spc>Conclusion
    and future work> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-28><vspace|0.5fn>

    <with|par-left|1.5fn|6.1<space|2spc>Reflections
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-29>>

    <with|par-left|1.5fn|6.2<space|2spc>Future work
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-30>>

    <with|par-left|3fn|6.2.1<space|2spc>Code coverage
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-31>>

    <with|par-left|3fn|6.2.2<space|2spc>Improved user feedback
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-32>>

    <with|par-left|3fn|6.2.3<space|2spc>KeY integration
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-33>>

    <with|par-left|3fn|6.2.4<space|2spc>Support for more frameworks
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-34>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|Bibliography>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-35><vspace|0.5fn>
  </table-of-contents>

  <new-page*>

  <section|Introduction>

  June 4th, 1996.\ 

  \;

  It is early afternoon, and despite the unmistakable advance of summer, a
  cloud canopy lingers over French Guiana.\ 

  \;

  The few rays that penetrate the cloud cover proceed to reflect off of the
  white-metallic hull of Ariane 5. She towers about 52 metres tall on the
  launch pad, her twin boosters already being prepared for her momentous next
  5 minutes. She is the latest marvel in European space exploration, the
  first of her kind, and has cost over <math|>370<math|> million USD to
  construct. With her, she carries 4 Cluster II satellites, which she over
  the next few hours will deploy in low orbit in order to help scientists
  study the interaction between cosmic rays and the earths magnetic field.
  \ Expectations from resident ESA officials could hardly have been higher.
  Somewhere in the control room, a napkin dries beads of sweat from the
  forehead of an operator. Maybe it's the heat.

  \;

  At 12:33:56 one of the French operators begins to anounce the last 10
  seconds of Arianes time on solid ground. The seconds pass by, the liftoff
  signal is given, her boosters flash and shake, and she ascends towards the
  skies, carried on a magnificient plume of burning rocket fuel. Her roars
  can be heard from kilometres away.\ 

  \;

  37 seconds later, the burning remains of Ariane 5 are falling back to
  ground she left just moments earlier. She has self-destructed in mid
  launch. Nobody is injured, but hundreds of millions of invested dollars
  have been lost in just a few seconds, and one of the ESA:s most prominent
  projects has suffered a catastophic setback. In the control room, more than
  a few napkins press against incredulous foreheads. The heat probably has
  very little to do with it right now.

  \;

  Ariane 5 is is dead, because somebody, in the course of her development,
  had assumed that it would be safe to round a 64-bit integer to a 16-bit
  representation.

  \;

  It wasn't. \ 

  <subsection|The pursuit of correctness>

  The Ariane 5 disaster<cite|jazequel1997design><cite|dowson1997ariane><cite|lions1996ariane>
  has become one of the flagship examples of the potentially disastrous
  consequences of <em|software failure>. Her demise emphasized the prominence
  of one of the great challenges in software engineering: the pursuit of
  <em|correctness> - assuring that a software system functions as intended.

  \;

  The advent of the Information Age has transformed human civilization like
  nothing else in our history. We now live in a world which is growing ever
  closer to irreversible dependence on computer technology, computers forming
  a part of almost every aspect of modern life, from supporting the very
  infrastructure of society, to helping individuals do their daily work and
  stay in contact with their friends and loved ones. As such, we deal with
  the consequences of software failure in some shape or form on an almost
  daily basis, although they most often will not be as serious as what
  happened to Ariane 5. Smartphones resetting, laptop screens going black,
  and word processors crashing (of course only when you forgot to enable
  document recovery), are all symptoms of software not being correct.\ 

  \;

  These examples are perhaps trivial at best, and their consequences are
  perhaps inconvenient at worst. The stakes rapidly scale up when we consider
  just how many critical elements of our modern societies depend on software.
  Software runs in life-support systems, medical instruments<\footnote>
    ADD NOTE ABOUT X-RAY DISASTER HERE
  </footnote>, emergency dispatch services, banking systems military
  appliances<\footnote>
    In 1991, during the Gulf War, a software failure in the then-deployed
    Patriot missile system caused it to fail to intercept an incoming SCUD
    ballistic missile, leading to the deaths of 28 soldiers, with scores more
    suffering injuries.
  </footnote>, nuclear reactors, airplanes, and rockets such as Ariane 5.
  It's crucial role in society means that its cost of failure runs a high
  risk of being counted in human lives and property. As such, the pursuit of
  correctness in software development is a topic well worth to prioritize.

  <subsection|Scope of this work>

  This work describes the implementation of the KeYTestGen2 automated test
  case generation system, as well as the theoretical concepts behind it. It
  aims to tackle the problem of software failure by providing a powerful
  addition to existing tools for software testing: the ability to
  automatically generate robust test suites. The end goal of this is to
  contribute to a more robust software engineering process, where developers
  will be able to spend more time developing software addressing the problems
  of the world, while letting tools such KeYTestGen2 ease the burden of
  verification.\ 

  \;

  The programming language targeted by KeYTestGen2, and hence also this
  thesis, is Java. The test framework we will focus on is JUnit, although
  KeYTestGen2 also has preliminary support for other frameworks as well.\ 

  <subsection|Organization>

  The body of this work is broken up into 5 sections.

  \;

  Section 2 is an introduction to the general theoretical concepts behind
  KeYTestGen2. Here we introduce software verification, testing, symbolic
  execution, and related concepts. This section is provided for the sake of
  context, and readers familiar with these concepts can ignore it, or refer
  to select parts.

  \;

  Section 3 gives paints a historical background for this work, and discusses
  related work.

  \;

  Section 4 gives an introduction to the KeY system, especially its Symbolic
  Debugging feature, which provides the essential symbolic execution services
  for KeYTestGen2.\ 

  \;

  Section 5 gives introduces KeYTestGen2 itself, describing its architecture
  and implementation.

  \;

  Section 6 provides a conclusion and discusses future work.

  <new-page*>

  <section|Fundamental concepts>

  In this section, we will set the context for the rest of the work by
  outlining the fundamental concepts relevant to it. We will begin by looking
  at verification and verification methods, focusing especially on
  <em|testing> as a verification method. We will formally define concepts
  central to testing itself, as well as the related testing quality metric
  known as <em|code coverage>. After that, we cover testing automation -
  first the automation of the test execution process, and then the central
  interest of this work: automating the test case generation process. We
  finish by introducing the KeY system, which forms the basis for
  KeYTestGen2.

  <subsection|Specifications - a formal look at correctness>

  Until now we have been content with using a rather loose definition of
  correctness, simply saying that software should ``function as intended''.
  Here, we will formalize this notion of correctness. To do so, we need to
  introduce the notion of a <em|specification>.

  \;

  <\with|par-left|1cm>
    <\framed>
      <\definition>
        \;

        \;

        A <with|font-series|bold|specification> for some code segment
        <with|font-series|bold|m> in some software system
        <with|font-series|bold|s> is a tuple\ 

        \ \ \ 

        \ \ \ \ \ \ \ \ (Pre, Post)

        \;

        where Pre (or <with|font-series|bold|preconditions>) is a set of
        constraints on the state of <with|font-series|bold|s> immediately
        prior to the execution of <with|font-series|bold|m>, and Post
        (<with|font-series|bold|postconditions>) is a set of constraints on
        the state of <with|font-series|bold|s> immediately after the
        execution of <with|font-series|bold|m> terminates, s.t. Pre -\<gtr\>
        Post (Post always holds given that Pre holds).

        \;

        By ``state of s'' we mean both the internal state of s itself, as
        well as any external factors which s depends on, such as a database,
        sensor, etc. <em|>\ 
      </definition>
    </framed>
  </with>

  \;

  \;

  Specifications are also commonly called <em|contracts>, since they specify
  a contractual relationship between software and the entity invoking it (the
  <em|callee> and <em|caller>). Under this contract, the callee gives certain
  guarantees (i.e. the postconditions) to the caller, given that the caller
  satisfies certain criteria (the preconditions) regarding how the call is
  made. \ 

  <subsubsection|The Java Modelling Language>

  In Java, specifications can be expressed informally as part of Javadoc
  comments<\footnote>
    It should be noted that the JavaDoc specification has native tags for
    expressing specifications, such as @pre and @inv. These are nowhere near
    expressive enough to write thorough specifications, however.
  </footnote> or ordinary comments. However, a more rigorous approach is to
  use a <with|font-shape|italic|specification language>. These are languages
  developed specifically for formulating rigorous and non-ambigous
  specifications for software.

  \;

  For Java, perhaps the most prominent such language is the Java Modelling
  Language; JML<cite|JMLwebsite><cite|JML-Ref-Manual>. JML is written inside
  ordinary Java comments for the code it relates to.\ 

  \;

  <\with|par-left|1cm>
    <\framed>
      <\example>
        \;

        \;

        The following is a specification for a simple addition function for
        positive intergers. The specification is expressed in the JML
        language.

        \;

        <\cpp>
          <\with|par-left|1cm>
            /*@ public spec normal_behavior

            \ \ @ requires x \<gtr\> 0 & y \<gtr\> 0

            \ \ @ ensures \\result == x + y \ & \\result \ \<gtr\> 0

            \ \ @*/

            public static void addWholePositive(int x, int y) {

            \ \ \ 

            \ \ \ if(x \<less\> 0 \|\| y \<less\> 0) {

            \ \ \ \ \ \ throw new IllegalArgumentException("Not a positive
            whole number");

            \ \ \ }

            \;

            \ \ \ return x + y;

            }
          </with>
        </cpp>

        \;

        The <with|font-series|bold|requires> clause here contain the
        preconditions, while the <with|font-series|bold|ensures> clause
        contains the postconditions. \\result denotes the value returned by
        the function. As can be easily seen here, this specification
        guarantees that the result will equal x+y and be greater than 0, if
        parameters x and y are both greater than 0 at the time of invocation.
        </example>
    </framed>
  </with>

  <subsection|Software verification and verification methods>

  \ \ In software development, the process of ensuring the correctness of
  software is called <em|verification><\footnote>
    Verification is a rich field of research and application all by itself,
    and we will only skim the surface here in order to create context for the
    rest of this work.
  </footnote>. A given approach to verifying software is called a
  <em|verification method>.

  <subsubsection|The verification ecosystem>

  Today, there is a wide array of verification methods available. To get an
  overview of the ecosystem they make up, we may classify them according to
  the <em|degree> <em|>of correctness they are intended to provide. We can
  think of them as spread across a spectrum, ranging from methods that take a
  rather lightweight and informal approach, to methods which are much more
  rigorous and approach mathematical precision in the kind of correctness
  they guarantee.\ 

  <subsubsection|The formal methods> \ 

  On the rigourous end of this spectrum we find the <em|formal methods>,
  which take a strict approach to correctness, generally requiring a
  mathematical or otherwise exhaustive demonstration that the software
  conforms to its specification.

  \;

  One prominent example of this approach is <em|deductive verification>,
  which treats the actual program code and its specification as part of some
  kind of logic, and uses a calculus for the same logic to deduce whether or
  not the code is correct with regard to the specification. The KeY system,
  which we will examine later, follows this approach.\ 

  Another widely used approach is <em|model checking>, which relies on
  constructing a model of the system, and then verifying properties of this
  model. If the properties can be shown to hold for the model, it (usually)
  follow that they hold for the software itself.

  \;

  The chief strength of formal methods is precisely their more complete
  approach to correctness: if a logical proof, validated model or equivalent
  can be obtained for some behavior of the software, we can be reasonably
  assured<\footnote>
    We can never be completely assured of this, as formal methods often only
    work on the source code level of the software itself. To assure 100%
    correctness, we would need to formally verify any underlying
    implementations as well, including compilers, interpreters, VMs and
    operating systems. Such extensive formal verification is usually
    infeasible.
  </footnote> that this behavior will always hold during runtime. For
  safety-critical applications, such as aircraft control systems, formal
  methods is often the desired approach to verification due to their demand
  for, practically, totally fail-safe operation.

  \;

  On the downside, formal verification is usually a resource heavy process,
  requiring special tool support, specialist training, and planning in order
  to be effectively deployed, or even feasible at all. Applying it to larger,
  or even general projects which do not require such a strict degree of
  correctness may thus not be a viable option.\ 

  <subsubsection|Software testing>

  On the other end, we find the various, informal <em|testing methods>. The
  basic idea behind these is executing the system - in whole or in part -
  with some well-defined input and subsequently analyzing the output of the
  execution, usually by comparing it to some expected output. Just what such
  expected output and well-defined input should be, is usually determined
  (respectively) by analyzing the postconditions and preconditions for the
  parts being tested.

  \;

  Testing methods benefit from being (much!) more intuitive and easy to use,
  as they embody what programmers normally do to check their code: specify
  some controlled input, execute the code, and determine if the output
  conforms to expected behavior. Due to this, testing is generally easier to
  adopt and use, as compared to the formal methods. The fundamental
  simplicity of testing also makes it a highly flexible process which easily
  scales to a wide range of applications.

  \;

  The simplistic and informal nature of testing, however, is also its chief
  weakness. Since testing is not exhaustive<\footnote>
    We can of course make testing exhaustive by constructing tests for
    <em|all> possible ways a system can perform a given task. However, it is
    obvious that this does not scale even for trivial programs. Furthermore,
    if we are looking for verification by exhaustive examination of possible
    executions, this is exactly what model checking is
  </footnote>, its degree of guaranteed correctness is far less than that of
  formal methods. As Edsgar Dijkstra put it,\ 

  <\quote-env>
    <em|``testing can demonstrate the presence of errors, but never their
    absence''>
  </quote-env>

  In other words, testing a system can helps us to locate bugs in it, but
  unlike a formal proof it can never give us any broader guarantees about the
  system actually being correct with regards to its specification.

  \;

  In terms of time and resources invested, testing is not always necessarily
  cheap, either. Writing test cases is an engineering discipline in its own
  right, and depending on the target extent of testing for a given system, it
  can in severe cases take more time to write tests for the system than the
  system itself.\ 

  Further, since the quality of a set of tests very much depend on how well
  it explores interesting execution paths in the system under test,
  considerable care has to be taken in order to avoid gaps in such coverage.
  All of this takes time, and in many cases, like with the formal methods,
  special training of team members responsible for testing. It is also very
  easy, despite all this, to get it wrong.\ 

  \;

  Despite its problems, the simplicity and flexibility of testing still makes
  it one of the most frequently used verification methods in the contemporary
  industry, enjoying a broad range of tool support and studies. In the
  present work, this is the manner of verification we will put the brunt of
  our focus on.

  <subsection|Unit testing>

  Testing can be done at several levels of granularity, ranging from testing
  the complete system, to testing interaction between modules, down to
  testing only atomic <em|units> of functionality
  <cite|SoftwareEngineering9>. In most programming languages, such units
  correspond to a function or routine (or method in an object oriented
  context). Testing such units is predictably called <em|unit testing>.

  \;

  A <em|test case> represents a single test for some unit in a software
  system. Formally, we define it like this:

  \;

  <\with|par-left|1cm>
    <\framed>
      <\definition>
        \;

        \;

        A <with|font-series|bold|test case> is a tuple (In, Or), where

        <\itemize>
          <item>In (``input'') is a tuple (P, S), where

          <\itemize-minus>
            <item>P is a set of parameter values to be passed to the unit,
            and

            <item>S is the state of the surrounding system as the unit starts
            executing.
          </itemize-minus>

          <item>Or (``oracle'') is a function Or(R, F) -\<gtr\> {true,
          false}, where\ 

          <\itemize-minus>
            <item>R is the return value of the unit (if any), and

            <item>F is the state of the system after the unit execution
            finishes.
          </itemize-minus>

          Or returns true if R and F match the expected system state after
          the unit terminates, and false otherwise.\ 
        </itemize>
      </definition>
    </framed>
  </with>

  \;

  \;

  During its execution cycle, a test case usually passes through the
  following stages <cite|TestPatterns2007>:

  <\enumerate-numeric>
    <item><with|font-shape|italic|Setup> a <with|font-shape|italic|test
    fixture>. Here, we set up everything that has to be in place in order for
    the test to run as intended. This includes instantiating the system as a
    whole to a desired state, as well as creating any necessary parameter
    values for the unit. \ 

    <item><with|font-shape|italic|Exercise> the test code. Here, we execute
    the unit itself with the parameters generated above, starting in the
    system state generated above.

    <item><with|font-shape|italic|Verify> the system state after the unit
    finishes executing. Here, we use a <with|font-shape|italic|test oracle> -
    a boolean function, to evaluate if the resulting state of the system
    satisfies our expectations. For example, for a method pushing an object
    to a stack, the oracle might verify that the stack has been incremented,
    and that the object on top is the object we expected to be pushed. \ 

    <item><with|font-shape|italic|Tear down> the test environment. Here, we
    undo whatever the previous 3 steps did to the system state, restoring it
    to a mint condition ready to accept another test case.
  </enumerate-numeric>

  \;

  Unit testing is a desirable level of granularity for many reasons. In
  particular, it can be used from the very beginning in most software
  engineering processes, since it requires only that the system contains a
  single unit to start writing tests for<\footnote>
    In fact, there are software engineering processes which are completely
    test-driven, and advocate writing the tests <em|before> the actual code
    is even implemented. A prominent example of such a process is
    <em|Test-Driven Development>.
  </footnote>. Further, unit testing is useful in debugging, as the cause for
  a test failing can be tracked down to a single unit and tackled there. This
  makes it an excellent tool for isolating regressions in the code as it is
  being developed and extended.\ 

  \;

  The remainder of this work assumes we are working in a unit testing
  environment, and this is the granularity we will have in mind whenever we
  mention testing for the remainder of it.

  <subsubsection|Test cases and test suites>

  A larger system will usually consist of hundreds - if not thousands - of
  individual units. Assuming we wish to create at least one test case for the
  non-trivial ones (getters, setters etc), we will quickly end up with a
  massive heap of tests to keep track of. The common approach in contemporary
  practice is to organize test cases into <em|test suites>, where each such
  test suite consists only of test cases for a given method, or a set of
  methods belonging to a module. Other ways of organizing test suites exist
  as well, and we do not endeavour to follow any given type of organization.\ 

  <subsection|Automating testing>

  The efficiency of unit testing can be augmented by using a <em|test
  framework>. One of the great benefits usually offered by such frameworks is
  the ability to <em|automate> large amounts of the testing process,
  especially the setting up of test environments and the execution of the
  tests themselves. The programmer can thus devote herself entirely to
  writing test suites, and then simply hand these over to the frameworks
  execution system for automatic runs, saving a lot of time and effort. It
  also means that the tests can easily be re-run without much efforts, which
  makes regression testing when refactoring or extending the system very
  easy, as the tests can simply be re-run repeatedly to verify that
  modifications to the system don't cause existing test suites to fail.

  \;

  <subsubsection|xUnit>

  While several test frameworks exist for unit testing, the most popular
  family of such frameworks is probably <em|xUnit>. Its Java implementation,
  called <em|JUnit>, is widely used in the Java development community.

  \;

  An xUnit // TODO

  <subsection|Automating test case generation>

  While test frameworks can help in automating the <em|execution> of test
  cases, they do not readily address the more expensive problem of
  <em|creating> them.\ 

  \;

  One attempt to solve overcome this hurdle are <em|test case generation
  systems>. Such systems will usually consume the source code along with some
  metadata about it (for example, constraints on the system state prior to
  the execution of the tests), and attempt to generate a set of tests for it
  depending on this information. Depending on what forms the basis of such
  test case generation, we can broadly classify into two main categories:
  black-box and white-box test generation.

  <subsubsection|Black box test generation>

  These systems work under the assumption that we do <em|not> have access to
  the source code itself, and as such will have to generate our test cases
  from some data <em|about> the code. In most cases, such metadata will be in
  the form of a <em|contract>, or <em|specification> for the code - a set of
  conditions that are promised to hold after the system finishes
  executing<\footnote>
    In reality, postconditions can of course be specified in such a way as to
    <em|not> demand that the execution actually terminates for them to hold.
  </footnote>, given that some other set of conditions hold before it starts
  execution. The former set of conditions are here called <em|preconditions>,
  the latter being <em|postconditions>.

  \;

  A black box system will usually analyze such pre- and postconditions, and
  use them to create program code corresponding to test cases. The
  precondition(s) will be broken down in order to find a representative set
  of input values, while the postcondition(s) likewise will be processed in
  order to produce code which will check the output of the test. Examples of
  systems using this approach are JMLUnitNG.\ 

  <subsubsection|White box test generation>

  Systems in this category work under the assumption that we <em|do> have
  access to the underlying source code. Knowing this gives us a much richer
  basis for test case generation, as we can now consider exploring the source
  code in order to extract information for creating more surgical tests, such
  as tests causing a given execution path to be taken, testing if a given
  statement is reachable, etc.

  \;

  \ How the source code is explored varies from system to system. A prominent
  approach is <em|symbolic execution>, which ``executes'' the code on a
  <em|symbolic> basis, i.e. without actually compiling or executing it.
  During symbolic execution, we walk the code statement by statement, mapping
  possible execution paths, and gathering interesting information about each
  statement in the code. This process can allow us, for example, to deduce
  the exact constraints on the program state for a given statement to be
  executed, allowing us to construct a test case which will reach this
  statement under actual runtime.\ 

  \;

  \ Importantly, only white box systems will allow us to generate tests which
  satisfy various <em|code coverage criteria> - a prominent metric for test
  case quality, measuring how much of the code is effectively covered by a
  set of tests. We discuss code coverage in the next subsection.

  <subsubsection|White box vs black box>

  White box test generation systems effectively subsume the functionality of
  black box ones, since they have access to all the data the latter use. On
  the downside, implementing symbolic execution (or some other method of
  exploring the source code) and related processing is usually non-trivial,
  and make white box systems much harder to implement then black box ones. \ 

  \;

  For the remainder of this work, we will consider a white box system, since
  it will give us access to the full range of features needed to facilitate
  robust test case generation. \ 

  <subsection|A metric for test quality: code coverage>

  Code coverage provides gives us a metric by which we can.\ 

  \;

  <\framed>
    <\with|par-left|1cm>
      <\example>
        \;
      </example>

      Consider the function:\ 

      \;

      <\cpp>
        \ \ \ int processBranch(int num) {

        \ \ \ \ \ \ switch(num) {

        \ \ \ \ \ \ \ \ \ case 1: return processOne();

        \ \ \ \ \ \ \ \ \ case 2: return processTwo();

        \ \ \ \ \ \ \ \ \ case 3: return processThree();

        \ \ \ \ \ \ }

        \ \ \ }
      </cpp>

      \;

      We construct the following test suite with some unspecified oracle:

      <with|font-shape|italic| \ T1: >(1, <with|font-shape|italic|oracle>)

      <with|font-shape|italic| \ T2: >(3, <with|font-shape|italic|oracle>)

      \;

      We can visualize the segments of code excercised by the test suite by
      drawing an execution tree for <with|font-series|bold|processBranch>.\ 

      \;

      <with|font-series|bold|[insert graphic]>

      \;

      Under this suite, the switch-branch triggered when num is 2 will never
      be taken. This is obviously problematic, since the invocation of
      <with|font-series|bold|processTwo()> could throw an exception, or
      affect the state of the system in an inadvert way.\ 
    </with>
  </framed>

  \;

  We see from the simple example above that the robustness of a test suite
  does not simply depend on excercising (even a large) set of possible input
  parameters. Rather, what is really significant is that we process a
  sufficient number of execution paths in the code itself.

  \;

  This leads us to the concept of <with|font-shape|italic|code coverage> - a
  formal criterion for what execution paths in the IUT have to be taken by
  executed by the test cases in a test suit . We say that a test suite
  fulfills a given code coverage criterion, iff there is at least one test
  case in the test suite which causes the specified branches to be executed.

  \;

  In contemporary industry and research a wide arrange of such criteria have
  been formulated. Generally, they are categorized as either
  <with|font-shape|italic|logic coverage criterion> or
  <with|font-shape|italic|graph coverage criterion>.\ 

  <subsubsection|Logic coverage>

  Logic coverage criteria are defined with regard to boolean decisions in the
  code.

  \;

  <\with|par-left|1cm>
    <\framed>
      <\definition>
        \;

        \;

        A <with|font-series|bold|condition> is an atomic boolean expression,
        i.e. it cannot be sub-divided into further boolean expressions. In
        many contemporary languages, examples of such include the standard
        comparison operators (\<less\>=, \<gtr\>=, \<less\>, \<gtr\>, ==,
        !=), boolean variables, and boolean functions.
      </definition>
    </framed>
  </with>

  \;

  \;

  <\with|par-mode|left>
    <\with|par-left|1cm>
      <\framed>
        <\definition>
          \;

          \;

          A <with|font-series|bold|decision> is a single condition, or a
          collection of conditions, connected by the standard logical
          operators <with|font-series|bold|AND >and
          <with|font-series|bold|><with|font-series|bold|OR> (often written
          && and \|\|, respectively).\ 
        </definition>
      </framed>
    </with>
  </with>

  \;

  \;

  <\with|par-left|1cm>
    <\framed>
      <\example>
        \;

        In Java, the following is a decision: (a && b) \|\| (!a &&
        (x\<less\>y)). Analysing its composition, we identify the following
        conditions:

        <\itemize-minus>
          <\itemize-dot>
            <item>Boolean variables <with|font-series|bold|a> and
            <with|font-series|bold|b>

            <item>Comparison x\<less\>y, where x and y are comparable
            (non-boolean) values.

            <item>The negation !a
          </itemize-dot>
        </itemize-minus>

        An important observation to make here, is that a and !a are
        <with|font-series|bold|separate> conditions, even though they both
        contain the same boolean variable a.
      </example>
    </framed>
  </with>

  <subsubsection|Graph coverage>

  Graph coverage critera are defined based on a
  <with|font-shape|italic|control flow graph> of the unit under test. In such
  a graph, a node represents a statement, and an edge a transition between.

  <\definition>
    \;

    \;

    A <with|font-series|bold|control flow graph> is a directed, possibly
    cyclic graph whose nodes are program statements, and whose edges are
    transitions between such statements. Each such edge has a
    <with|font-series|bold|transitional condition>, which is a boolean
    decision that must hold in the first node of the edge, in order for the
    transition to be taken. \ 
  </definition>

  <\definition>
    \;

    A test suite TS satisfies statement coverage, if and only if
  </definition>

  <subsection|Symbolic execution>

  The clear benefit of using the Symbolic Debugger is that it provides a very
  helpful abstraction on top of KeY:s proof representation, in order to make
  it easier to reason about execution paths.

  <new-page*>

  <section|Background>

  We are now done with much of the introduction of the fundamental concepts,
  and ready to dive into our solution of all the problems of the world -
  KeYTestGen. In this section, we provide a historical context for this work,
  discussing the various theoretical developments leading up to it. We also
  discuss similar solutions in the field.

  <subsection|Early work - KeY and the Verification Based Test Generator>

  The idea to use KeYs symbolic execution engine for test case generation was
  initially explored by Gladisch et al <cite|BeckertGladisch2007>. A master
  thesis was later produced at Chalmers, providing a reference implementation
  <cite|Engel2006>. At this stage, this method for automated test case
  generation was termed <with|font-shape|italic|verification based test
  generation> <cite|EngelHaehnle07>.

  \;

  This early work used the fact that the proof process of KeY, in particular
  the symbolic execution driving it, contained enough information for mapping
  the possible execution paths through a given JavaCard program. This came as
  a natural consequence of the soundness of the dynamic logic
  <cite|Beckert01> used to reason about proof obligations in KeY - if certain
  paths were indiscernible, this would in turn mean that it would not be
  possible to prove something which should hold with regard to the source
  code. Thus, in the course of a proof, the system would consider (on a
  symbolic level) every possible path that could be taken from the execution
  of any given statement. This formed the basis for the
  <with|font-shape|italic|path analysis> part of the test generation
  processs.

  \;

  Moreover, for any such path, KeY made it possible to extract a
  <with|font-shape|italic|path condition> - a set of constraints on the
  initial state of they system which had to hold in order for that particular
  path to be taken in the course of execution. The constraints in these path
  conditions, in turn, could be used in order to create concrete data that
  satisfied them, and thus made ensured that the execution path would be
  taken. This, naturally, was the basis for <with|font-shape|italic|fixture
  generation> in the test generation process.

  \;

  Generating test fixtures was a non-trivial process. Integer data types
  could effectively be generated using constraint solving. In this case, an
  SMT solver would be used to find a counterexample to the negation of a
  given pathcondition, and concrete values would then be extracted from this
  result. For booleans, an algorithm working on equivalance classes of
  available boolean fields could be applied directly to establish a working
  resultant set. Reference types could be obtained (at least on the
  theoretical level) in an analogous fashion. At this stage, floats were not
  supported, due to limitation of the KeY system.

  \;

  Apart from the full automation of the process itself, one of the most
  powerful contributions of VBT was the ability to obtain very high levels of
  code coverage, including the industrial strength MCDC criterion (which is
  used, for example, in the avionics industry). This followed directly from
  the thorough examination of possible execution paths throughout the proof
  process itself. Almost as a side effect to this rigourous exploration,
  issues such as the <with|font-shape|italic|inner variable problem> were
  addressed as well.

  \;

  Limitations existed on the reach of VBT as well. Apart from floats not
  being supported, certain core language features, such as statics, were
  disallowed as well. More relevant to our work, intricate Object type
  problems, such as implicit state dependencies between classes, were not
  addressed, which could potentially lead to erroneous test conditions being
  generated.

  <new-page*>

  <section|The KeY system>

  We now move on to consider the implementation of KeYTestGen itself. We
  begin by introducing the KeY system, in particular its Symbolic Debugger,
  which provide the symbolic execution technology upon which KeYTestGen
  itself is implemented.

  <subsection|KeY - an overview>

  KeY <cite|KeYwebsite><cite|KeY2005><cite|ahrendt2007key> is an

  <new-page*>

  <section|KeYTestGen2>

  //TODO

  <new-page*>

  <section|Conclusion and future work>

  Automated test case generation tools can provide a significant productivity
  boost to most software engineering processes, since they allow for the
  automation of otherwise time consuming elements of development and
  validation. Moreover, the more advanced crop of such tools can provide
  powerful benefits such as code coverage, leading to test suite robustness
  which is both hard and resource heavy to do manually.

  \;

  Here, we provide reflections on the design and overall contribution of our
  tool, and give an overview of ongoing and future developments.

  <subsection|Reflections>

  <subsection|Future work>

  KeYTestGen is under continous development, and the present work at best
  represents an early prototype of what we would like it to be. At a more
  mature stage, we firmly believe KeYTestGen can establish itself as a
  powerful tool in the software engineering community, especially as an
  integrated part of the KeY system itself. To reach such maturity, of
  course, very much will still have to be done.\ 

  <subsubsection|Code coverage>

  <\with|par-mode|left>
    <\with|par-mode|justify>
      In its current state, KeYTestGen only generates test suites providing a
      primitive kind of statement coverage. To make it useful in actual
      development, it is desireable to provide at the very least the common
      forms<\footnote>
        i.e. statemen, branch, condition and decision coverage.
      </footnote>, as well as at least one industrial-grade coverage
      criteria, such as MCDC.\ 
    </with>
  </with>

  \;

  To facilitate this, algorithms need to be developed which can consume a
  symbolic execution tree and return a set of nodes which would suffice for
  satisfying such criteria. We are not aware of any such algorithms at this
  stage (if they exist, they are most likely language specific). At face
  value, the algorithms themselves appear rather simple to develop. A more
  problematic issue is choosing whether to work directly with the symbolic
  execution tree, or using an intermediate representation instead. The latter
  is most likely desireable due to the potentially enormous complexity of
  symbolic execution trees, but how to construct such a representation has
  not been well thought out at this stage.\ 

  <subsubsection|Improved user feedback>

  Since KeYTestGen performs an extensive analysis of the source code it
  consumes (due to symbolic execution), we see the possibility of the tool
  providing extensive feedback to the user about the quality of the code.\ 

  \;

  For example, the tool could potentially detect more subtle runtime errors
  which are otherwise caught neither by the compiler nor signaled by
  exceptions at runtime. One such case would be statements which are
  unreachable due to their path conditions being unsatisfiable. Example 10
  demonstrates one such case.

  \;

  <\framed>
    <\example>
      \;

      \;

      An unreachable statement: <strong|return x;>

      <\cpp-code>
        int a = 5;

        int b = 4;

        if(a \<gtr\> b) {

        \ \ \ if(b \<gtr\> a) {

        \ \ \ \ \ \ return x;

        \ \ \ }

        }
      </cpp-code>
    </example>
  </framed>

  \ \ \ 

  \;

  Since a \<gtr\> b and a \<less\> b are mutually exclusive expressions, the
  statement return x; can never be executed under normal conditions. Such
  anomalies are certainly results of a mistake in the development process,
  and something the developer would like to get notified about.

  <subsubsection|KeY integration>

  Integration of KeYTestGen with the main KeY system has been an objective
  from the beginning. In particular, close integration between the Symbolic
  Debugger of KeY and KeYTestGen has been targeted. From the perspective of
  the debugger, KeYTestGen could be invoked in order to generate individual
  test cases for specific execution nodes. From the perspective of
  KeYTestGen, the debugger could, for example, be invoked dynamically in
  order to assist the user in resolving situations where certain degrees of
  code coverage cannot be satisfied due to errors in the design of th code
  itself.

  <subsubsection|Support for more frameworks>

  Currently, KeYTestGen supports generating test suites for the JUnit
  framework. In the long term, we aim to implement support for other test
  frameworks as well. The next iteration in this area will most likely target
  the TestNG <cite|TestNGwebsite> framework.

  \;

  It is noteworthy that both JUnit and TestNG are primarily designed for unit
  testing. As far as possible, it would be interesting to explore the
  possibilities of generating test cases of higher granularity, such as
  integration tests. Doing so would of course require much more indepth
  analysis of the code itself, along with possible manual input from the user
  (such as specifications on class inte

  gration, etc).

  //TODO

  <nocite|Gladisch2012>

  <nocite|Gladisch2010>

  <nocite|Gladisch2010_TAP>

  <nocite|AhrendtEtAl2009>

  <nocite|BubelEtAl2009>

  <nocite|BeckertEtAl2008>

  <nocite|Gladisch2008>

  <nocite|EngelEtAl2008>

  <nocite|Gladisch2008_TAP>

  <nocite|AhrendtEtAl2007>

  <nocite|HahnleEtAl2010>

  <new-page*>

  <\bibliography|bib|tm-plain|literature.bib>
    <\bib-list|24>
      <bibitem*|1><label|bib-AhrendtEtAl2007>Wolfgang<nbsp>Ahrendt,
      Bernhard<nbsp>Beckert, Reiner<nbsp>Hähnle,
      Philipp<nbsp>Rümmer<localize| and >Peter H.<nbsp>Schmitt.<newblock>
      Verifying object-oriented programs with KeY: a tutorial.<newblock>
      <localize|In ><with|font-shape|italic|5th International Symposium on
      Formal Methods for Components and Objects, Amsterdam, The Netherlands>,
      <localize|volume> 4709<localize| of ><with|font-shape|italic|LNCS>,
      <localize|pages >70--101. Springer, 2007.<newblock>

      <bibitem*|2><label|bib-AhrendtEtAl2009>Wolfgang<nbsp>Ahrendt,
      Richard<nbsp>Bubel<localize| and >Reiner<nbsp>Hähnle.<newblock>
      Integrated and tool-supported teaching of testing, debugging, and
      verification.<newblock> <localize|In >J.<nbsp>Gibbons<localize| and >J.
      N.<nbsp>Oliveira<localize|, editors>, <with|font-shape|italic|Proc.
      Second International Conference on Teaching Formal Methods>,
      <localize|volume> 5846<localize| of ><with|font-shape|italic|LNCS>,
      <localize|pages >125--143. Springer, 2009.<newblock>

      <bibitem*|3><label|bib-Beckert01>Bernhard<nbsp>Beckert.<newblock> A
      Dynamic Logic for the formal verification of Java Card
      programs.<newblock> <localize|In >I.<nbsp>Attali<localize| and
      >T.<nbsp>Jensen<localize|, editors>, <with|font-shape|italic|Java on
      Smart Cards: Programming and Security. Revised Papers, Java Card 2000,
      International Workshop, Cannes, France>, LNCS 2041, <localize|pages
      >6--24. Springer, 2001.<newblock>

      <bibitem*|4><label|bib-BeckertGladisch2007>Bernhard<nbsp>Beckert<localize|
      and >Christoph<nbsp>Gladisch.<newblock> White-box testing by combining
      deduction-based specification extraction and black-box
      testing.<newblock> <localize|In >Bertrand<nbsp>Meyer<localize| and
      >Yuri<nbsp>Gurevich<localize|, editors>, <with|font-shape|italic|Proc.
      Tests and Proofs, Zürich, Switzerland>, LNCS. Springer-Verlag, to
      appear, 2007.<newblock>

      <bibitem*|5><label|bib-TestNGwebsite>Cédric<nbsp>Beust.<newblock>
      TestNG home page.<newblock> <href|Http://testng.org/doc/index.html>.<newblock>

      <bibitem*|6><label|bib-BubelEtAl2009>Richard<nbsp>Bubel,
      Reiner<nbsp>Hähnle<localize| and >Benjamin<nbsp>Weiss.<newblock>
      Abstract interpretation of symbolic execution with explicit state
      updates.<newblock> <localize|In >Frank<nbsp>de<nbsp>Boer, Marcello
      M.<nbsp>Bonsangue<localize| and >Eric<nbsp>Madelaine<localize|,
      editors>, <with|font-shape|italic|Post Conf. Proc. 6th International
      Symposium on Formal Methods for Components and Objects (FMCO)>,
      <localize|volume> 5751<localize| of ><with|font-shape|italic|LNCS>,
      <localize|pages >247--277. Springer-Verlag, 2009.<newblock>

      <bibitem*|7><label|bib-BeckertEtAl2008>Special issue on tests and
      proofs.<newblock> <with|font-shape|italic|Journal of Automated
      Reasoning>, , 2008.<newblock> To appear.<newblock>

      <bibitem*|8><label|bib-JMLwebsite>The JML<nbsp>community.<newblock> JML
      home page.<newblock> <href|Http://www.eecs.ucf.edu/>.<newblock>

      <bibitem*|9><label|bib-KeYwebsite>The KeY<nbsp>community.<newblock> The
      KeY project - integrated deductive software design.<newblock>
      <href|Http://www.key-project.org>.<newblock>

      <bibitem*|10><label|bib-dowson1997ariane>M.<nbsp>Dowson.<newblock> The
      ariane 5 software failure.<newblock> <with|font-shape|italic|ACM
      SIGSOFT Software Engineering Notes>, 22(2):84, 1997.<newblock>

      <bibitem*|11><label|bib-Engel2006>Christian<nbsp>Engel.<newblock>
      Verification based test case generation.<newblock> <localize|Master's
      thesis>, Universität Karlsruhe, aug 2006.<newblock>

      <bibitem*|12><label|bib-EngelEtAl2008>Christian<nbsp>Engel,
      Christoph<nbsp>Gladisch, Vladimir<nbsp>Klebanov<localize| and
      >Philipp<nbsp>Rümmer.<newblock> Integrating Verification and Testing of
      Object-Oriented Software.<newblock> <localize|In
      >Bernhard<nbsp>Beckert<localize| and >Reiner<nbsp>Hähnle<localize|,
      editors>, <with|font-shape|italic|Tests and Proofs. Second
      International Conference, TAP 2008, Prato, Italy>, LNCS 4966. Springer,
      2008.<newblock>

      <bibitem*|13><label|bib-EngelHaehnle07>Christian<nbsp>Engel<localize|
      and >Reiner<nbsp>Hähnle.<newblock> Generating unit tests from formal
      proofs.<newblock> <localize|In >Bertrand<nbsp>Meyer<localize| and
      >Yuri<nbsp>Gurevich<localize|, editors>, <with|font-shape|italic|Proc.
      Tests and Proofs (TAP), Zürich, Switzerland>, LNCS. Springer, to
      appear, 2007.<newblock>

      <bibitem*|14><label|bib-Gladisch2008_TAP>Christoph<nbsp>Gladisch.<newblock>
      Verification-based test case generation with loop invariants and method
      specifications.<newblock> <localize|Technical Report>, University of
      Koblenz-Landau, 2008.<newblock>

      <bibitem*|15><label|bib-Gladisch2008>Christoph<nbsp>Gladisch.<newblock>
      Verification-based testing for full feasible branch coverage.<newblock>
      <localize|In >Antonio<nbsp>Cerone<localize|, editor>,
      <with|font-shape|italic|Proc. 6th IEEE Int. Conf. Software Engineering
      and Formal Methods (SEFM'08)>. IEEE Computer Society Press,
      2008.<newblock>

      <bibitem*|16><label|bib-Gladisch2010>Christoph<nbsp>Gladisch.<newblock>
      Test data generation for programs with quantified first-order logic
      specifications.<newblock> <localize|In ><cite|DBLP:conf/pts/2010>,
      <localize|pages >158--173.<newblock>

      <bibitem*|17><label|bib-Gladisch2012>Christoph<nbsp>Gladisch.<newblock>
      Model generation for quantified formulas with application to test data
      generation.<newblock> <with|font-shape|italic|International Journal on
      Software Tools for Technology Transfer (STTT)>, :1--21, feb
      2012.<newblock> 10.1007/s10009-012-0227-0.<newblock>

      <bibitem*|18><label|bib-HahnleEtAl2010>R.<nbsp>Hähnle, M.<nbsp>Baum,
      R.<nbsp>Bubel<localize| and >M.<nbsp>Rothe.<newblock> A visual
      interactive debugger based on symbolic execution.<newblock>
      <localize|In ><with|font-shape|italic|Proceedings of the IEEE/ACM
      international conference on Automated software engineering>,
      <localize|pages >143--146. ACM, 2010.<newblock>

      <bibitem*|19><label|bib-jazequel1997design>J.M.<nbsp>Jazequel<localize|
      and >B.<nbsp>Meyer.<newblock> Design by contract: the lessons of
      ariane.<newblock> <with|font-shape|italic|Computer>, 30(1):129--130,
      1997.<newblock>

      <bibitem*|20><label|bib-JML-Ref-Manual>Gary T.<nbsp>Leavens,
      Erik<nbsp>Poll, Curtis<nbsp>Clifton, Yoonsik<nbsp>Cheon,
      Clyde<nbsp>Ruby, David<nbsp>Cok, Peter<nbsp>Müller,
      Joseph<nbsp>Kiniry<localize| and >Patrice<nbsp>Chalin.<newblock>
      <with|font-shape|italic|JML Reference Manual. Draft Revision
      1.200>.<newblock> Feb 2007.<newblock>

      <bibitem*|21><label|bib-lions1996ariane>J.L.<nbsp>Lions
      et<nbsp>al.<newblock> Ariane 5 flight 501 failure.<newblock>
      1996.<newblock>

      <bibitem*|22><label|bib-TestPatterns2007>Gerard<nbsp>Meszaros.<newblock>
      <with|font-shape|italic|XUnit Test Patterns>.<newblock> Addison-Wesley
      Signature Series. Addison-Wesley, 2007.<newblock>

      <bibitem*|23><label|bib-DBLP:conf/pts/2010>Alexandre<nbsp>Petrenko,
      Adenilso<nbsp>da<nbsp>Silva Simão<localize| and >José
      Carlos<nbsp>Maldonado<localize|, editors>.<newblock>
      <with|font-shape|italic|Testing Software and Systems - 22nd IFIP WG 6.1
      International Conference, ICTSS 2010, Natal, Brazil, November 8-10,
      2010. Proceedings>, <localize|volume> 6435<localize| of
      ><with|font-shape|italic|Lecture Notes in Computer Science>.<newblock>
      Springer, 2010.<newblock>

      <bibitem*|24><label|bib-SoftwareEngineering9>Ian<nbsp>Sommerville.<newblock>
      <with|font-shape|italic|Software Engineering>.<newblock> Pearson
      International, 9th<localize| edition>, 2011.<newblock>
    </bib-list>
  </bibliography>
</body>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|4>>
    <associate|auto-10|<tuple|2.2.2|7>>
    <associate|auto-11|<tuple|2.2.3|8>>
    <associate|auto-12|<tuple|2.3|8>>
    <associate|auto-13|<tuple|2.3.1|8>>
    <associate|auto-14|<tuple|2.4|9>>
    <associate|auto-15|<tuple|2.4.1|9>>
    <associate|auto-16|<tuple|2.5|10>>
    <associate|auto-17|<tuple|2.5.1|10>>
    <associate|auto-18|<tuple|2.5.2|10>>
    <associate|auto-19|<tuple|2.5.3|10>>
    <associate|auto-2|<tuple|1.1|4>>
    <associate|auto-20|<tuple|2.6|11>>
    <associate|auto-21|<tuple|2.6.1|12>>
    <associate|auto-22|<tuple|2.6.2|12>>
    <associate|auto-23|<tuple|2.7|13>>
    <associate|auto-24|<tuple|3|13>>
    <associate|auto-25|<tuple|3.1|14>>
    <associate|auto-26|<tuple|4|14>>
    <associate|auto-27|<tuple|4.1|15>>
    <associate|auto-28|<tuple|5|16>>
    <associate|auto-29|<tuple|6|16>>
    <associate|auto-3|<tuple|1.2|5>>
    <associate|auto-30|<tuple|6.1|16>>
    <associate|auto-31|<tuple|6.2|16>>
    <associate|auto-32|<tuple|6.2.1|16>>
    <associate|auto-33|<tuple|6.2.2|17>>
    <associate|auto-34|<tuple|6.2.3|17>>
    <associate|auto-35|<tuple|6.2.4|18>>
    <associate|auto-36|<tuple|6.2.4|?>>
    <associate|auto-37|<tuple|6.2.4|?>>
    <associate|auto-4|<tuple|1.3|5>>
    <associate|auto-5|<tuple|2|6>>
    <associate|auto-6|<tuple|2.1|6>>
    <associate|auto-7|<tuple|2.1.1|6>>
    <associate|auto-8|<tuple|2.2|7>>
    <associate|auto-9|<tuple|2.2.1|7>>
    <associate|bib-AhrendtEtAl2007|<tuple|1|18>>
    <associate|bib-AhrendtEtAl2009|<tuple|2|18>>
    <associate|bib-Beckert01|<tuple|3|18>>
    <associate|bib-BeckertEtAl2008|<tuple|7|18>>
    <associate|bib-BeckertGladisch2007|<tuple|4|18>>
    <associate|bib-BubelEtAl2009|<tuple|6|18>>
    <associate|bib-DBLP:conf/pts/2010|<tuple|23|18>>
    <associate|bib-Engel2006|<tuple|11|18>>
    <associate|bib-EngelEtAl2008|<tuple|12|18>>
    <associate|bib-EngelHaehnle07|<tuple|13|18>>
    <associate|bib-Gladisch2008|<tuple|15|18>>
    <associate|bib-Gladisch2008_TAP|<tuple|14|18>>
    <associate|bib-Gladisch2010|<tuple|16|18>>
    <associate|bib-Gladisch2012|<tuple|17|18>>
    <associate|bib-HahnleEtAl2010|<tuple|18|?>>
    <associate|bib-JML-Ref-Manual|<tuple|20|18>>
    <associate|bib-JMLwebsite|<tuple|8|18>>
    <associate|bib-KeYwebsite|<tuple|9|18>>
    <associate|bib-SoftwareEngineering9|<tuple|24|18>>
    <associate|bib-TestNGwebsite|<tuple|5|18>>
    <associate|bib-TestPatterns2007|<tuple|22|18>>
    <associate|bib-dowson1997ariane|<tuple|10|?>>
    <associate|bib-jazequel1997design|<tuple|19|?>>
    <associate|bib-lions1996ariane|<tuple|21|?>>
    <associate|footnote-1|<tuple|1|5>>
    <associate|footnote-2|<tuple|2|5>>
    <associate|footnote-3|<tuple|3|6>>
    <associate|footnote-4|<tuple|4|7>>
    <associate|footnote-5|<tuple|5|7>>
    <associate|footnote-6|<tuple|6|8>>
    <associate|footnote-7|<tuple|7|8>>
    <associate|footnote-8|<tuple|8|10>>
    <associate|footnote-9|<tuple|9|16>>
    <associate|footnr-1|<tuple|1|5>>
    <associate|footnr-2|<tuple|2|5>>
    <associate|footnr-3|<tuple|3|6>>
    <associate|footnr-4|<tuple|4|7>>
    <associate|footnr-5|<tuple|5|7>>
    <associate|footnr-6|<tuple|6|8>>
    <associate|footnr-7|<tuple|7|8>>
    <associate|footnr-8|<tuple|8|10>>
    <associate|footnr-9|<tuple|9|16>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|bib>
      jazequel1997design

      dowson1997ariane

      lions1996ariane

      JMLwebsite

      JML-Ref-Manual

      SoftwareEngineering9

      TestPatterns2007

      BeckertGladisch2007

      Engel2006

      EngelHaehnle07

      Beckert01

      KeYwebsite

      KeY2005

      ahrendt2007key

      TestNGwebsite

      Gladisch2012

      Gladisch2010

      Gladisch2010_TAP

      AhrendtEtAl2009

      BubelEtAl2009

      BeckertEtAl2008

      Gladisch2008

      EngelEtAl2008

      Gladisch2008_TAP

      AhrendtEtAl2007

      HahnleEtAl2010

      DBLP:conf/pts/2010
    </associate>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Introduction>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|1.1<space|2spc>The pursuit of correctness
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2>>

      <with|par-left|<quote|1.5fn>|1.2<space|2spc>Scope of this work
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>>

      <with|par-left|<quote|1.5fn>|1.3<space|2spc>Organization
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Fundamental
      concepts> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|2.1<space|2spc>A formal look at
      correctness <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6>>

      <with|par-left|<quote|3fn>|2.1.1<space|2spc>The Java Modelling Language
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7>>

      <with|par-left|<quote|1.5fn>|2.2<space|2spc>Software verification and
      verification methods <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>>

      <with|par-left|<quote|3fn>|2.2.1<space|2spc>The verification ecosystem
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-9>>

      <with|par-left|<quote|3fn>|2.2.2<space|2spc>The formal methods
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10>>

      <with|par-left|<quote|3fn>|2.2.3<space|2spc>Software testing
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11>>

      <with|par-left|<quote|1.5fn>|2.3<space|2spc>Unit testing
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-12>>

      <with|par-left|<quote|1.5fn>|2.4<space|2spc>Test cases and test suites
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-13>>

      <with|par-left|<quote|1.5fn>|2.5<space|2spc>Automating testing
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14>>

      <with|par-left|<quote|1.5fn>|2.6<space|2spc>Automating test case
      generation <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-15>>

      <with|par-left|<quote|3fn>|2.6.1<space|2spc>Black box test generation
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-16>>

      <with|par-left|<quote|3fn>|2.6.2<space|2spc>White box test generation
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-17>>

      <with|par-left|<quote|3fn>|2.6.3<space|2spc>White box vs black box
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-18>>

      <with|par-left|<quote|1.5fn>|2.7<space|2spc>A metric for test quality:
      code coverage <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-19>>

      <with|par-left|<quote|3fn>|2.7.1<space|2spc>Logic coverage
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-20>>

      <with|par-left|<quote|3fn>|2.7.2<space|2spc>Graph coverage
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-21>>

      <with|par-left|<quote|1.5fn>|2.8<space|2spc>Symbolic execution
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-22>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Background>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-23><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|3.1<space|2spc>Early work - KeY and the
      Verification Based Test Generator <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-24>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>The
      KeY system> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-25><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|4.1<space|2spc>KeY - an overview
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-26>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>KeYTestGen2>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-27><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|6<space|2spc>Conclusion
      and future work> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-28><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|6.1<space|2spc>Reflections
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-29>>

      <with|par-left|<quote|1.5fn>|6.2<space|2spc>Future work
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-30>>

      <with|par-left|<quote|3fn>|6.2.1<space|2spc>Code coverage
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-31>>

      <with|par-left|<quote|3fn>|6.2.2<space|2spc>Improved user feedback
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-32>>

      <with|par-left|<quote|3fn>|6.2.3<space|2spc>KeY integration
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-33>>

      <with|par-left|<quote|3fn>|6.2.4<space|2spc>Support for more frameworks
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-34>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Bibliography>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-35><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>