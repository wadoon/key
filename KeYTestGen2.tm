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

    <with|par-left|1.5fn|2.1<space|2spc>Defining ``correctness''
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-6>>

    <with|par-left|3fn|2.1.1<space|2spc>The Java Modelling Language
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-7>>

    <with|par-left|1.5fn|2.2<space|2spc>Software verification and
    verification methodss <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
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

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|5<space|2spc>KeYTestGen2>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-26><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|6<space|2spc>Conclusion
    and future works> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-27><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|Bibliography>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-28><vspace|0.5fn>
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

  Ariane 5 is is dead, because somebody assumed that it would be safe to
  round a 64-bit integer to a 16-bit representation.

  \;

  It wasn't. \ 

  <subsection|The pursuit of correctness>

  The Ariane 5 disaster has become one of the flagship examples of the
  potentially disastrous consequences of <em|software failure>. She is far
  from the only one, but she emphasized one of the great challenges in
  software engineering: the pursuit of <em|correctness> - assuring that a
  software system functions as intended.

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
  case generation system and the theoretical concepts behind it. It aims to
  tackle the problem of software failure by providing a powerful addition to
  existing tools for software testing: the ability to automatically generate
  robust test suites. The end goal of this is to contribute to a more robust
  software engineering process, where developers will be able to spend more
  time developing software addressing the problems of the world, while
  letting tools such KeYTestGen2 ease the burden of verification.\ 

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

  <subsection|Defining ``correctness''>

  Until now we have been content with using a rather loose definition of
  correctness, simply saying that software should ``function as intended''.
  Here, we will formalize this notion of correctness. To do so, we need to
  introduce the notion of a <em|specification>.

  <\with|par-left|1cm>
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
      constraints on the state of <with|font-series|bold|s> immediately prior
      to the execution of <with|font-series|bold|m>, and Post
      (<with|font-series|bold|postconditions>) is a set of constraints on the
      state of <with|font-series|bold|s> immediately after the execution of
      <with|font-series|bold|m> terminates, s.t. Pre -\<gtr\> Post (Post
      always holds given that Pre holds).

      \;

      By ``state of s'' we mean both the internal state of s itself, as well
      as any external factors which s depends on, such as a database, sensor,
      etc. <em|>\ 
    </definition>
  </with>

  Specifications are also commonly called <em|contracts>, since they specify
  a contractual agreement between a code segment and the entity invoking it.
  The invoked piece of code gives certain guarantees (i.e. the
  postconditions) to its caller, given that the caller satisfies certain
  criteria (the preconditions) in relation to the call. \ 

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
  Language; JML <cite|JML-Ref-Manual>. JML is written inside ordinary Java
  comments for the code it relates to.\ 

  <\with|par-left|1cm>
    <\example>
      \;

      \;

      The following is a specification for a simple addition function for
      positive intergers. The specification is expressed in the JML language.

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
      contains the postconditions. \\result denotes the value returned by the
      function.
    </example>
  </with>

  \;

  <subsection|Software verification and verification methodss>

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
  think of them spread as across a spectrum, ranging from methods that take a
  rather lightweight and informal approach to correctness, to methods which
  are much more rigorous and give extensive guarantees in regard to
  correctness.

  <subsubsection|The formal methods> \ 

  On the rigourous end of this spectrum we find the <em|formal methods>,
  which take a strict approach to correctness, generally requiring a
  mathematical or otherwise exhaustive demonstration that a given behavior of
  the software is upheld during runtime.\ 

  \;

  One prominent example of this approach is <em|deductive verification>,
  which treats the actual program code as part of some kind of logic, and
  uses a calculus for the same logic to deduce whether or not the code is
  correct. The KeY system, which we will examine later, follows this
  approach. Another widely used approach is <em|model checking>, which relies
  on constructing a model of the system, and then verifying properties of
  this model. If the properties can be shown to hold for the model, it
  (usually) follow that they hold for the software itself.

  \;

  The chief strength of formal methods is their more complete approach to
  correctness: if a logical proof, validated model or equivalent can be
  obtained for some behavior of the software, we can be reasonably
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
  for practically total correctness.\ 

  \;

  On the downside, formal verification is usually a resource heavy process,
  requiring special tool support, specialist training, and planning in order
  to be effectively deployed. Applying it to larger, or even general projects
  which do not require such a strict degree of correctness may thus not be a
  viable option.\ 

  <subsubsection|Software testing>

  On the other end, we find the various <em|testing methods>, which rely on
  executing parts of the system and analyzing the output, usually comparing
  it to some set of accepted or expected output.

  \;

  Testing methods benefit from being much more intuitive and easy to use, as
  they embody what programmers normally do to check the functionality of
  their code: specify some controlled input, execute the code, and determine
  if the output corresponds to expected behavior. Testing thus offers a more
  natural approach to verification (from the programmers perpective), making
  it easier to adopt and use, as compared to the formal methods. The
  fundamental simplicity of testing also makes it a highly flexible process
  which easily scales to a wide range of applications.

  \;

  The simplistic and informal nature of testing is also its chief weakness.
  Since testing is not exhaustive<\footnote>
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
  systems behavior.\ 

  \;

  In terms of time and resources invested, testing is not necessarily cheap
  either. Writing test cases can an engineering discipline in its own right.
  Depending on the scope of the testing, it can in severe cases take up more
  time and actual coding effort than what is invested in the actual system
  itself. Since the quality of a set of tests very much depend on how well it
  explores interesting execution paths in the system under test, considerable
  care has to be taken in order to avoid gaps in what the tests cover. All of
  this takes time, and in many cases, like with the formal methods, special
  training of team members responsible for testing. It is also very easy,
  despite all this, to get it wrong.\ 

  \;

  Despite its problems, the many benefits (especially the flexibility) of
  testing still make it one of the most frequently used verification methods
  in the contemporary industry, and it is our main focus in the present work.\ 

  <subsection|Unit testing>

  Testing can be done at several levels of granularity, ranging from testing
  the complete system to testing only atomic units of
  functionality<cite|SoftwareEngineering9>. In most programming languages,
  such units correspond to a function/routine (or method in an object
  oriented context). Testing such units is predictably called <em|unit
  testing>.

  \;

  Unit testing is a desirable level of granularity for many reasons. In
  particular, it can be deployed immediately, since it requires only a single
  unit of functionality to start writing tests for<\footnote>
    In fact, there are software engineering processes which are completely
    test-driven, and advocate writing the tests <em|before> the actual code
    is even implemented. A prominent example of such a process is
    <em|Test-Driven Development>.
  </footnote>. Further, it is useful for making the search for bugs as narrow
  as possible, as the cause for a test failing can in this case be tracked
  down to a single unit. The remainder of this work assumes we are working in
  a unit testing environment, and this is the granularity we will have in
  mind whenever we mention testing for the remainder of it.

  <subsection|Test cases and test suites>

  To approach testing in a structured way, we will here provide a formal
  definition for how we structure our unit tests, in terms of <em|test cases>
  and <em|test suites>.

  \;

  \ A test case represents a single test for some unit in a software system.
  It will pass through the following lifecycle<cite|TestPatterns2007>:

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

  Formally, we define a test case like this:

  <\with|par-left|1cm>
    <\definition>
      \;

      \;

      A <with|font-series|bold|test case> is a tuple (In, Or), where

      <\itemize>
        <item>In (``input'') is a tuple (P, S), where

        <\itemize-minus>
          <item>P is a set of parameter values to be passed to the unit, and

          <item>S is the state of the surrounding system as the unit starts
          executing.
        </itemize-minus>

        <item>Or (``oracle'') is a function Or(R, F) -\<gtr\> {true, false},
        where\ 

        <\itemize-minus>
          <item>R is the return value of the unit (if any), and

          <item>F is the state of the system after the unit execution
          finishes.
        </itemize-minus>

        Or returns true if R and F match the expected system state after the
        unit terminates, and false otherwise.\ 
      </itemize>
    </definition>
  </with>

  \;

  A <em|test suite> is simply a collection of test cases for a given method.

  <subsection|Automating testing>

  The efficiency of testing can be augmented by using one of several open
  source, industrial strength <em|test frameworks>. One of the great benefits
  usually offered by such frameworks is the ability to <em|automate> large
  amounts of the testing process, especially the setting up of test
  environments and the execution of the tests themselves. The programmer can
  thus devote herself entirely to writing test suites, and then simply hand
  these over to frameworks execution system for automatic runs, saving a lot
  of time and effort. It also means that the tests can easily be re-run
  without much efforts, which makes regression testing when refactoring or
  extending the system very easy. The tests can simply be re-run to verify
  that modifications to the system don't cause existing test suites to fail.

  \;

  While several test frameworks exist for unit testing, the most popular
  family of such frameworks is probably <em|xUnit>. Its Java implementation,
  called <em|JUnit>, is widely used in the Java development community.

  <subsection|Automating test case generation>

  While test frameworks can help in automating the <em|execution> of test
  cases, they do not readily address the more expensive problem of
  <em|creating> them. It would be desirable if we could somehow automate this
  process as well, at least partially.

  \;

  One attempt to solve this are so-called <em|test case generation systems>.
  Such systems will usually consume the source code along with some metadata
  about it (for example, constraints on the system state prior to the
  execution of the tests), and attempt to generate a set of tests for it
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

    Under this suite, the switch-branch triggered when num is 2 will never be
    taken. This is obviously problematic, since the invocation of
    <with|font-series|bold|processTwo()> could throw an exception, or affect
    the state of the system in an inadvert way.\ 
  </with>

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

  <\with|par-left|1cm>
    <\definition>
      \;

      \;

      A <with|font-series|bold|condition> is an atomic boolean expression,
      i.e. it cannot be sub-divided into further boolean expressions. In many
      contemporary languages, examples of such include the standard
      comparison operators (\<less\>=, \<gtr\>=, \<less\>, \<gtr\>, ==, !=),
      boolean variables, and boolean functions.
    </definition>
  </with>

  <\with|par-mode|left>
    <\with|par-left|1cm>
      <\definition>
        \;

        \;

        A <with|font-series|bold|decision> is a single condition, or a
        collection of conditions, connected by the standard logical operators
        <with|font-series|bold|AND >and <with|font-series|bold|><with|font-series|bold|OR>
        (often written && and \|\|, respectively).\ 
      </definition>
    </with>
  </with>

  <\with|par-left|1cm>
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

  In this section, we provide a historical context for this work, discussing
  the various theoretical developments leading up to it. We also discuss
  similar solutions in the field.

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

  //TODO

  <new-page*>

  <section|KeYTestGen2>

  //TODO

  <new-page*>

  <section|Conclusion and future works>

  //TODO

  <new-page*>

  <\bibliography|bib|tm-plain|literature.bib>
    <\bib-list|7>
      <bibitem*|1><label|bib-Beckert01>Bernhard<nbsp>Beckert.<newblock> A
      Dynamic Logic for the formal verification of Java Card
      programs.<newblock> <localize|In >I.<nbsp>Attali<localize| and
      >T.<nbsp>Jensen<localize|, editors>, <with|font-shape|italic|Java on
      Smart Cards: Programming and Security. Revised Papers, Java Card 2000,
      International Workshop, Cannes, France>, LNCS 2041, <localize|pages
      >6--24. Springer, 2001.<newblock>

      <bibitem*|2><label|bib-BeckertGladisch2007>Bernhard<nbsp>Beckert<localize|
      and >Christoph<nbsp>Gladisch.<newblock> White-box testing by combining
      deduction-based specification extraction and black-box
      testing.<newblock> <localize|In >Bertrand<nbsp>Meyer<localize| and
      >Yuri<nbsp>Gurevich<localize|, editors>, <with|font-shape|italic|Proc.
      Tests and Proofs, Zürich, Switzerland>, LNCS. Springer-Verlag, to
      appear, 2007.<newblock>

      <bibitem*|3><label|bib-Engel2006>Christian<nbsp>Engel.<newblock>
      Verification based test case generation.<newblock> <localize|Master's
      thesis>, Universität Karlsruhe, aug 2006.<newblock>

      <bibitem*|4><label|bib-EngelHaehnle07>Christian<nbsp>Engel<localize|
      and >Reiner<nbsp>Hähnle.<newblock> Generating unit tests from formal
      proofs.<newblock> <localize|In >Bertrand<nbsp>Meyer<localize| and
      >Yuri<nbsp>Gurevich<localize|, editors>, <with|font-shape|italic|Proc.
      Tests and Proofs (TAP), Zürich, Switzerland>, lncs. Spv, to appear,
      2007.<newblock>

      <bibitem*|5><label|bib-JML-Ref-Manual>Gary T.<nbsp>Leavens,
      Erik<nbsp>Poll, Curtis<nbsp>Clifton, Yoonsik<nbsp>Cheon,
      Clyde<nbsp>Ruby, David<nbsp>Cok, Peter<nbsp>Müller,
      Joseph<nbsp>Kiniry<localize| and >Patrice<nbsp>Chalin.<newblock>
      <with|font-shape|italic|JML Reference Manual. Draft Revision
      1.200>.<newblock> Feb 2007.<newblock>

      <bibitem*|6><label|bib-TestPatterns2007>Gerard<nbsp>Meszaros.<newblock>
      <with|font-shape|italic|XUnit Test Patterns>.<newblock> Addison-Wesley
      Signature Series. Addison-Wesley, 2007.<newblock>

      <bibitem*|7><label|bib-SoftwareEngineering9>Ian<nbsp>Sommerville.<newblock>
      <with|font-shape|italic|Software Engineering>.<newblock> Pearson
      International, 9th<localize| edition>, 2011.<newblock>
    </bib-list>
  </bibliography>
</body>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|2>>
    <associate|auto-10|<tuple|2.2.2|6>>
    <associate|auto-11|<tuple|2.2.3|6>>
    <associate|auto-12|<tuple|2.3|7>>
    <associate|auto-13|<tuple|2.4|7>>
    <associate|auto-14|<tuple|2.5|8>>
    <associate|auto-15|<tuple|2.6|8>>
    <associate|auto-16|<tuple|2.6.1|8>>
    <associate|auto-17|<tuple|2.6.2|8>>
    <associate|auto-18|<tuple|2.6.3|9>>
    <associate|auto-19|<tuple|2.7|9>>
    <associate|auto-2|<tuple|1.1|2>>
    <associate|auto-20|<tuple|2.7.1|10>>
    <associate|auto-21|<tuple|2.7.2|10>>
    <associate|auto-22|<tuple|2.8|11>>
    <associate|auto-23|<tuple|3|11>>
    <associate|auto-24|<tuple|3.1|12>>
    <associate|auto-25|<tuple|4|13>>
    <associate|auto-26|<tuple|5|14>>
    <associate|auto-27|<tuple|6|15>>
    <associate|auto-28|<tuple|6|?>>
    <associate|auto-3|<tuple|1.2|3>>
    <associate|auto-4|<tuple|1.3|3>>
    <associate|auto-5|<tuple|2|4>>
    <associate|auto-6|<tuple|2.1|4>>
    <associate|auto-7|<tuple|2.1.1|5>>
    <associate|auto-8|<tuple|2.2|5>>
    <associate|auto-9|<tuple|2.2.1|5>>
    <associate|bib-Beckert01|<tuple|1|15>>
    <associate|bib-BeckertGladisch2007|<tuple|2|15>>
    <associate|bib-Engel2006|<tuple|3|15>>
    <associate|bib-EngelHaehnle07|<tuple|4|15>>
    <associate|bib-JML-Ref-Manual|<tuple|5|?>>
    <associate|bib-SoftwareEngineering9|<tuple|7|15>>
    <associate|bib-TestPatterns2007|<tuple|6|15>>
    <associate|footnote-1|<tuple|1|2>>
    <associate|footnote-2|<tuple|2|3>>
    <associate|footnote-3|<tuple|3|3>>
    <associate|footnote-4|<tuple|4|5>>
    <associate|footnote-5|<tuple|5|6>>
    <associate|footnote-6|<tuple|6|6>>
    <associate|footnote-7|<tuple|7|7>>
    <associate|footnote-8|<tuple|8|8>>
    <associate|footnote-9|<tuple|9|?>>
    <associate|footnr-1|<tuple|1|2>>
    <associate|footnr-2|<tuple|2|3>>
    <associate|footnr-3|<tuple|3|3>>
    <associate|footnr-4|<tuple|4|5>>
    <associate|footnr-5|<tuple|5|6>>
    <associate|footnr-6|<tuple|6|6>>
    <associate|footnr-7|<tuple|7|7>>
    <associate|footnr-8|<tuple|8|8>>
    <associate|footnr-9|<tuple|9|?>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|bib>
      JML-Ref-Manual

      SoftwareEngineering9

      TestPatterns2007

      BeckertGladisch2007

      Engel2006

      EngelHaehnle07

      Beckert01
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

      <with|par-left|<quote|1.5fn>|2.1<space|2spc>Defining ``correctness''
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6>>

      <with|par-left|<quote|3fn>|2.1.1<space|2spc>The Java Modelling Language
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7>>

      <with|par-left|<quote|1.5fn>|2.2<space|2spc>Software verification and
      verification methodss <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
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

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>KeYTestGen2>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-26><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|6<space|2spc>Conclusion
      and future works> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-27><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Bibliography>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-28><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>