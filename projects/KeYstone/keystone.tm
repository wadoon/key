<TeXmacs|1.0.7.18>

<style|article>

<\body>
  <doc-data|<doc-title|KeYstone: a <with|font-shape|italic|fast> mixed-type,
  non-linear constraint solver for the KeY
  system>|<doc-author|<author-data|<author-name|Christopher
  Svanefalk>|<\author-affiliation>
    \;

    <strong|<with|font-base-size|14|University of Gothenburg>>

    Department of Computer Science and Engineering

    \;

    \;
  </author-affiliation>>>>

  <abstract-data|<\abstract>
    This work presents KeYstone, a constraint solver designed for operation
    within the KeYTestGen2 verification-based test case generation system.
    Its role is to optimize the overall performance of KeYTestGen2 by
    resolving a crucial bottleneck - the generation of primitive numeric test
    data, a process which explicitly requires linear programming.

    \;

    Since KeYstone is domain specific, it is free to optimize its behavior
    only with respect to KeYTestGen2 itself. The end of this is a solving
    process which should, optimally, perform better than any general solver
    which could be used for the same purpose.
  </abstract>>

  <new-page*>

  <\table-of-contents|toc>
    <vspace*|1fn><with|font-series|bold|math-font-series|bold|1<space|2spc>Introduction>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-1><vspace|0.5fn>

    <with|par-left|1.5fn|1.1<space|2spc>The KeY system
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-2>>

    <with|par-left|1.5fn|1.2<space|2spc>KeYTestGen2
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-3>>

    <with|par-left|1.5fn|1.3<space|2spc>Test data generation in KeYTestGen2
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-4>>

    <with|par-left|3fn|1.3.1<space|2spc>Object and boolean values
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-5>>

    <with|par-left|3fn|1.3.2<space|2spc>Numeric types
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-6>>

    <with|par-left|1.5fn|1.4<space|2spc>Performance issues
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-7>>

    <with|par-left|3fn|1.4.1<space|2spc>Execution time
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-8>>

    <with|par-left|3fn|1.4.2<space|2spc>Memory usage
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-9>>

    <with|par-left|3fn|1.4.3<space|2spc>Addressing performance
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-10>>

    <with|par-left|1.5fn|1.5<space|2spc>Contribution of this work
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-11>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|2<space|2spc>Design>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-12><vspace|0.5fn>

    <with|par-left|1.5fn|2.1<space|2spc>Assumptions
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-13>>

    <with|par-left|1.5fn|2.2<space|2spc>Branch-and-bound
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-14>>

    <with|par-left|1.5fn|2.3<space|2spc>Pre-processing
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-15>>

    <with|par-left|1.5fn|2.4<space|2spc>Solving
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-16>>

    <with|par-left|3fn|2.4.1<space|2spc>Basics
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-17>>

    <with|par-left|3fn|2.4.2<space|2spc>Eliminating inequalities
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-18>>

    <with|par-left|3fn|2.4.3<space|2spc>Simplifying the system
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-19>>

    <with|par-left|3fn|2.4.4<space|2spc>Solving the system
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-20>>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|3<space|2spc>Implementation>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-21><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|4<space|2spc>Discussion>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-22><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|5<space|2spc>Conclusion>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-23><vspace|0.5fn>

    <vspace*|1fn><with|font-series|bold|math-font-series|bold|Bibliography>
    <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
    <no-break><pageref|auto-24><vspace|0.5fn>
  </table-of-contents>

  <page-break*><section|Introduction>

  <with|font-shape|italic|Constraint problems> represent one of the most
  common problems in both applied mathematics and general human life and
  industry. The essence of such problems is to find a legitimate assignment
  of values to a set of variables, subject to some set of constraints. Such
  an assignmet is frequently required to be
  <with|font-shape|italic|optimized>, i.e. consist of either a minimal set of
  values, or a maximum one.\ 

  \;

  A prominent mathematic approach to addressing such problems is known as
  <with|font-shape|italic|linear programming>. Under this method, such
  problems can be formalized in the following way:

  \;

  [todo]

  \;

  Problems of this kind have an important application in the KeYTestGen2 test
  case generation system, where they // TODO

  \;

  For the sake of context, we provide brief introductions to both KeY and
  KeYTestGen2 below.\ 

  <subsection|The KeY system>

  KeY <cite|KeY2005> is a formal verification system, targetting<\footnote>
    Third-party support exists for C <cite|MLH07>, as well as Java bytecode.
  </footnote> a subset of Java known as Java Card. It operates by translating
  JML-annotated<\footnote>
    While it is not longer supported as of KeY 2.0, certain older versions of
    KeY have partial support for the OCL specification language.
  </footnote> Java Card code into a proof obligation expressed in the dynamic
  logic JavaCard DL <cite|Beckert01>. A semi-interactive theorem prover is
  then applied to this proof obligation, with the goal of proving that the
  preconditions of the code imply its postconditions. Such a proof is carried
  out by means of <with|font-shape|italic|symbolic execution> of the source
  code, where the actual JC code is translated - statement by statement -
  into its <with|font-shape|italic|logical> effect on the state of the
  program. It thus has to be demonstrated that, given a specific pre-state of
  the program (as defined in the programs specification), the execution of
  the code itself must necessarily bring the program into a given post-state
  (also defined in the specification). If such a correlation can be made, a
  proof can be presented that the program fulfills its
  specification<\footnote>
    Naturally, this does not imply that the operation of the program will
    necessarily be free of error, as that would require the formal
    verification of the operating system, hardware, and anything else
    involved in the execution of the program as well.
  </footnote>.

  <subsection|KeYTestGen2>

  For certain programs, a rigorous proof of correctness is sometimes not
  desireable, or even feasible. This can be due to several reasons, such as
  time constraints (formal verification can, in certain cases, be a
  notoriously resource consuming process), the sheer size of the system
  itself, or overall \ expectations on reliability being too low to justify
  such an approach.\ 

  \;

  In such cases, KeY offers a less formal, but fully automatic approach known
  as <with|font-shape|italic|verification-based test case generation> (VBT)
  <cite|EngelHaehnle07>. Here, the proof <with|font-shape|italic|information>
  generated by KeY is harnessed in order to create very robust
  <with|font-shape|italic|test suites> for the software, rather than a formal
  proof. These test suites can be generated for a variety of popular test
  frameworks, such as JUnit and TestNG, and thus be seamlessly integrated
  into the existing test code for the software.

  \;

  VBT is made possible due to how the KeY proof process works. For the sake
  of soundness, KeY has to completely, symbolically execute the code being
  verified. In so doing, it has to explore
  <with|font-shape|italic|all><\footnote>
    It is important to note here that this does not generally apply to loop
    structures, which may have an infinite number of possible execution
    paths. For such structures, KeY requires that the user provides a
    <with|font-shape|italic|loop invariant>, on the basis of which
    conclusions can be made regarding the logical effects of the loop.
  </footnote> the possible execution paths which may be taken through the
  code. This exploration further allows it to gather data about the paths
  being visited, including constraints on the pre-state of the program for a
  given path to be taken, i.e. the paths <with|font-shape|italic|path
  condition>. The program can then be caused to follow a given execution path
  simply by starting it in a state which satisfies that paths path condition.

  \;

  The possibility to generate tests for individual execution paths makes VBT
  very powerful, since it enables us to generate tests based on various
  code-coverage criteria, which normally is not possible in most test case
  generation systems. For example, KeYTestGen2 has experimental support for
  the Modified Condition / Decision Coverage (MCDS) criterion, which among
  other things is required by the aviation industry for testing
  <with|font-shape|italic|class A> software, i.e. software whose failure is
  deemed ``catastrophic''.

  \;

  In KeY, VBT is realized through the KeYTestGen system <cite|Paganelli2010>.
  A more advanced system, KeYTestGen2, is in an experimental state, and will
  be the focus of this work. One of the significant ways in which it differs
  from its predecessor is by making use of another KeY project, the Symbolic
  Visual Debugger (SVD), in order to encapsulate the process of of gathering
  data about possible execution paths.\ 

  <subsection|Test data generation in KeYTestGen2>

  In order to create a test case for a given execution path in a program,
  KeYTestGen2 has to generate a program pre-state satisfying the path
  condition of that path. In other words, concrete value assignments need to
  be found for the program variables constrained by the path condition. In
  Java, such variables can be of either object, boolean, or numeric
  type<\footnote>
    Boolean and numeric types are both considered primitive types in Java.\ 
  </footnote>. How values of each are generated vary.

  <subsubsection|Object and boolean values>

  Reference and boolean values can both be generated directly from the path
  condition itself, as the only logical operator applicable to such types is
  equality. Hence, a constraint on a boolean variable will only be an
  assignment of <with|font-series|bold|true> or
  <with|font-series|bold|false>. Likewise, a constraint on an object will
  only be an assignment of <with|font-series|bold|null>, or a reference to a
  concrete object on the heap. KeYTestGen2 simply extracts such assignments,
  and translates them to concrete Java code.

  <subsubsection|Numeric types>

  Numeric types are not nearly as succint as objects or booleans, as we now
  potentially have to deal with inequalities. For such, no direct value
  assignment can be extracted (as in the case of an equality) - instead a set
  of value assignments needs to be calculated which satisfies all involved
  inequalities.

  \;

  In KeYTestGen2, this is currently solved by using an SMT solver. Here, the
  path condition is pruned of non-numeric constraints, negated, translated
  into the SMT-LIB format (recognized by most prominent SMT solvers), and
  passed to the given solver. The solver in turn finds a counter-example to
  the negation, which corresponds to the needed set of value assignments.
  Finally, these assignments are extracted, associated with their
  corresponding variables, and translated into Java code.

  \;

  As of current, KeYTestGen2 uses a modified version of the SMTInterpol
  solver, which executes natively on the same JVM. It also features support
  for external solvers, such as Microsofts Z3, by means of an interface
  provided by KeY itself.

  <subsection|Performance issues>

  While the above outlined approach to test data generation works, it is
  questionable how optimal it is. The current approach to numeric test data
  generation suffers on several points.

  <subsubsection|Execution time>

  On a relatively powerful benchmark system (Stock-speed 12-core Intel i7
  3930K, 16GB DDR3 RAM), finding a solution even for trivial path conditions
  (less than 3 inequalities to solve) takes the native solver 600-1000ms.
  This rapidly grows into a serious performance bottleneck with more complex
  programs, since these may require several dozens - if not hundreds - of
  test cases in order to reach acceptable levels of code coverage.

  <subsubsection|Memory usage>

  A major problem with the native solver is that it does not work at all in a
  concurrent context. Unfortunately, KeYTestGen2 is a highly parallelized
  system where multiple threads are almost constantly in need of using it. In
  practice, this means that each such thread will have to create a new
  instance of the solver and run it - a process which can allocate up to
  200MB of RAM. To prevent the JVM from crashing due to lack of memory, this
  allocation is itself synchronized to prevent the allocation of too
  many<\footnote>
    This threshold value is configurable, but defaults to 3.
  </footnote> solvers concurrently. \ 

  <subsubsection|Addressing performance>

  Both issues above can to some extent be mitigated through using an external
  solver, such as Microsofts Z3. This is made possible by means of an SMT
  interface provided by KeY itself. There are several problems with this
  approach, however:

  <\itemize-dot>
    <item>It imposes a dependence on third-party, non-Java, potentially
    proprietary solvers for KeYTestGen2 to even work.

    <item>While it does partially address the memory issues (solvers written
    in C/C++, as expected, generally appear to use less memory than their
    Java counterparts), it does not significantly address the execution
    speed. The difference in execution times between Z3 and the native solver
    are almost neglible, the stronger performance of Z3 being offset by
    overhead imposed by the SMT interface and the fact that it has to run in
    an OS process.\ 
  </itemize-dot>

  Due to these reasons alone, it is desirable that a new solution is found
  for the generation of numeric test data in KeYTestGen2.

  <subsection|Contribution of this work>

  This work was is an an attempt to overcome the performance issues discussed
  earlier, by implementing a solver tailored directly to the context of
  KeYTestGen2 and KeY itself. By being domain specific, such a solver could
  be uniquely optimized to its intended purpose, and ideally outperform all
  current solutions.

  \;

  This work describes such a solver, under the working name KeYstone. We will
  begin with a description of the linear programming algorithm used by this
  solver (section 2), followed by a description of how it is implemented
  (section 3). We conclude with a comparison between KeYstone and existing
  solvers, together with a discussion (section 4), and finally give some
  concluding remarks (section 5).

  <new-page*><section|Design>

  In this section, we outline the constraint solving algorithm used in
  KeYstone, along with its fundamental assumptions.

  <subsection|Assumptions>

  The KeYstone algorithm is based on the following assumptions:

  <\enumerate-numeric>
    <item><with|font-series|bold|A solution always exists> - this necessarily
    follows from the soundness of KeYs proof process, and the filtering
    taking place in the SVD. If a given execution branch through the code is
    infeasible, it will not be part of the symbolic execution tree returned
    by the SVD. Thus, any path which we can extract from the symbolic
    execution tree has a path condition for which we can find at least one
    satisfiable assignment. \ 

    <item><with|font-series|bold|All variables are integers> - this follows
    from the fact that neither JavaCard nor KeY as of yet support floating
    point values. KeYTestGen2 hence never has to deal with them.
  </enumerate-numeric>

  <subsection|Pre-processing>

  Before executing the solving process, we will attempt to optimize the
  problem in order to minimize the actual work to be done. Such optimization
  is carried out using an intuitive heuristic, by which we attempt to isolate
  the smallest subset of the <with|font-shape|italic|simplest> constraints to
  be solved in order to satisfy the entire path condition. The procedure is
  outlined below:

  \;

  <\framed>
    <\algorithm>
      Let P be an execution path, and let C<rsub|P> be P:s path condition,
      s.t. C<rsub|P> consists only of equalities, inequalities and arithmetic
      operations over the real numbers. Further, let CM<rsub|P> be the set of
      numeric comparators in C<rsub|P>.\ 

      \;

      We find the <with|font-shape|italic|minimal problem set> M<rsub|P> of
      P, s.t. M<rsub|P> <math|\<subseteq\>> CM<rsub|P>, in the following way:

      <\render-code>
        <with|font-series|bold|function> optimize(<math|\<phi\>>:Term):[Term]:

        \ \ \ \ <with|font-series|bold|case> <math|\<phi\>>:

        \ \ \ \ \ \ \ \ <with|font-series|bold|<math|\<Psi\>>> \ \ \ \ \ \ :
        <with|font-series|bold|return> <math|\<Psi\>><rsub|>

        \ \ \ \ \ \ \ \ <math|\<Psi\> \ \ \<wedge\> \ \ \<Phi\>> :
        <with|font-series|bold|return> optimize(<math|\<Psi\>>) +
        optimize(<math|\<Phi\>>)

        \ \ \ \ \ \ \ \ <math|\<Psi\> \ \ \<vee\> \ \ \<Phi\>> :
        <with|font-series|bold|if> price(<math|\<Psi\>>) <math|\<leq\>>
        price(<math|\<Phi\>>):\ 

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|return>
        optimize(<math|\<Psi\>>)

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|else>:

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|return>
        optimize(<math|\<Phi\>>)\ 

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|end if>

        \ \ \ \ <with|font-series|bold|end case>

        <with|font-series|bold|end function>
      </render-code>
    </algorithm>
  </framed>

  \;

  The crucial element of the algorithm above is the
  <with|font-series|bold|price<with|font-shape|italic|>> function, which
  determines how ``heavy'' a sub-problem is to solve in the context of the
  entire path condition. Since our goal is to collect the smallest number of
  ``light'' problems, this function needs to be carefully designed<\footnote>
    Note that as of this version of this document (and KeYstone), this
    algorithm is very primitive, and simply chooses a set of sub-problems in
    such a way that we will have as few problems as possible, and as few
    variables as possible. While this may intuitively be a good result, it is
    very likely that it can be done (much) better. This will have to wait
    until future iterations due to time constraints.
  </footnote>.

  \;

  <\framed>
    <\algorithm>
      Given the definitions for algorithm 1, along with the following:

      \ \ \ \ 

      \ \ \ \ let Vars be the set of variables over the real numbers

      \ \ \ \ let Comps be the set of binary, arithmetic comparators

      \ \ \ \ let vars(<math|\<phi\>>):[x \| x <math|\<in\>> Vars] be the set
      of variables in problem <math|\<phi\>>,\ 

      \ \ \ \ let comps(<math|\<phi\>>):[x \| x <math|\<in\>> Comps] be the
      set of arithmetic comparators in problem <math|\<phi\>>,

      \;

      we determine the <with|font-shape|italic|weight> of a problem
      SP<rsub|P> in P the following way:

      \;

      \ \ \ \ <with|font-series|bold|function> price(<math|\<phi\>>):Integer

      \ \ \ \ \ \ \ \ <with|font-series|bold|let> VAR_PRICE = 2

      \ \ \ \ \ \ \ \ <with|font-series|bold|return> price\ 

      \ \ \ \ \ <with|font-series|bold|end function>

      <\render-code>
        <with|font-series|bold|function> price_gather(<math|\<phi\>>:Term,
        V:[Variable]):(Integer,[Variable])

        \ \ \ \ <with|font-series|bold|let> PROBLEM_PRICE = 1

        \ \ \ \ <with|font-series|bold|case> <math|\<phi\>>:

        \ \ \ \ \ \ \ \ <with|font-series|bold|<math|\<Psi\>>>
        \ \ \ \ \ \ \ <math|\<Rightarrow\>> <with|font-series|bold|return>
        (PROBLEM_PRICE, vars(<with|font-series|bold|<math|\<Psi\>>>));

        \ \ \ \ \ \ \ \ <math|\<Psi\> \ \ \<wedge\> \ \ \<Phi\>>
        \ <math|\<Rightarrow\>>\ 

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|let>
        left_tuple = price_gather(<math|\<Psi\>>);

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|let>
        right_tuple = price_gather(<math|\<Phi\>>);

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|return>
        (first(left_tuple) + first(right_tuple),\ 

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ union(second(left_tuple),
        second(right_tuple));

        \ \ \ \ \ \ \ \ <math|\<Psi\> \ \ \<vee\> \ \ \<Phi\>>
        \ <math|\<Rightarrow\>>\ 

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|let>
        left_tuple = price_gather(<math|\<Psi\>>);

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|let>
        right_tuple = price_gather(<math|\<Phi\>>);

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|if>
        evaluate(left_tuple) <math|\<leq\>> evaluate(right_tuple):\ 

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|return>
        left_tuple;

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|else>:

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|return>
        right_tuple;\ 

        \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|end if>
        \ \ \ \ \ \ \ <with|font-series|bold|>

        \ \ \ \ <with|font-series|bold|end case>

        <with|font-series|bold|end function>

        \;

        <with|font-series|bold|function> evaluate(T:(Integer,
        [Variable])):Integer

        \ \ \ \ <with|font-series|bold|return> first(T) + length(second(T))\ 

        <with|font-series|bold|end function>
      </render-code>
    </algorithm>
  </framed>

  \;

  <subsection|Solving>

  Geometrically speaking, a set of inequalities form an n-dimensional
  polytope, bounding the feasible solution space for the set. Many well-known
  algorithms, such as the simplex algorithm, find a maximized or minimized
  solution for inequalities by walking the vertices of their corresponding
  polytope.

  \;

  In our case, we are not interested in an <with|font-shape|italic|optimal>
  (i.e. minimized or maximized) solution, but will settle for
  <with|font-shape|italic|any> solution (subject to some criteria, see
  below). This is justified by two key observations:

  \;

  <\enumerate-numeric>
    <item>A maximized or minimized solution offers practically no benefit at
    all to the operation of KeYTestGen2 itself. If a program requires, say,
    that 2x<math|\<less\>>y holds for some program variables x and y in order
    for a given path to be executed, then it does not matter if the generated
    solution is (x=0, y=1) or (x=1073741823, y=2147483647).

    <item>The task of finding a maximized or minimized solution can incur
    (potentially enormous) computational overhead to the solving process.
    Further, it (usually) requires both the algorithm and corresponding
    implementation to be made even more complex than they need to be.\ 
  </enumerate-numeric>

  \;

  As such, the goal of our algorithm is simply to retrieve the
  <with|font-shape|italic|first feasible solution> available. For a solution
  to be deemed feasible - apart from, of course, satisfying the constraints -
  it has to satisfy the following criteria:

  \ 

  <\enumerate-numeric>
    <item>For each variable in the path condition, the corresponding value in
    the result must be within the legal range of the Java type of that
    variable. For example, for integers, the value must lie between
    -2<rsup|32> and 2<rsup|32>-1.
  </enumerate-numeric>

  \;

  We now outline the algorithm for determining such a solution - an algorithm
  which turns out to be extremely simple compared to other linear programming
  ones.

  <subsubsection|Basics>

  The central idea of our algorithm is to solve a system of regular equations
  (either linear or polynomial) in order to obtain values for all required
  variables. To do so, we need to do the following:

  \;

  <\enumerate-numeric>
    <item>Eliminate inequalities from the path condition.

    <item>Simplify the resulting equations.

    <item>Solve the resulting equations and extract values.
  </enumerate-numeric>

  \;

  <subsubsection|Eliminating inequalities>

  A system of inequalities can be transformed into an equivalent system of
  equalities by introducing extra variables<\footnote>
    Formally, these are known as <with|font-shape|italic|slack variables>
    (for less-or-equals inequalities) and <with|font-shape|italic|surplus
    variables> (for greater-or-equals). We do not make such a distinction
    here, as it is not relevant to the algorithm.
  </footnote>. Each such variable corresponds to the difference between the
  left and right hand sides of the corresponding inequality - i.e. the number
  needed to ``even out'' the inequality, effectively turning it into an
  equality.\ 

  \;

  <\framed>
    <\example>
      \;

      \;

      Consider:\ 

      <\equation*>
        2x \<noplus\>+4y-z \<leq\>10
      </equation*>

      The extra variable <math|s<rsub|1>> can be subtracted from to the right
      hand side, in order to eliminate the inequality:

      <\equation*>
        2x \<noplus\>+4y-z=10-s<rsub|1>
      </equation*>

      Finally, we simplify this to:

      <\equation*>
        2x \<noplus\>+4y-z +s<rsub|1>=10
      </equation*>
    </example>
  </framed>

  \;

  \;

  The intuition here is that <math|s<rsub|1>> is the value which will need to
  be added to the left hand side, in order to bring it into equality with the
  right hand side. The same intuition holds for the opposite case:\ 

  \;

  <\framed>
    <\example>
      \;

      \;

      Consider example 1 again, but this this time let the inequality be
      greater-or-equals instead:

      <\equation*>
        2x \<noplus\>+4y-z \<geqslant\>10
      </equation*>

      The extra variable <math|s<rsub|1>> is introduced as before, but this
      time it is added to the right hand side.

      <\equation*>
        2x \<noplus\>+4y-z =10 \<noplus\>+s<rsub|1>
      </equation*>

      This in turn simplifies to:

      <\equation*>
        2x \<noplus\>+4y-z -s<rsub|1>=10
      </equation*>
    </example>
  </framed>

  \;

  It is important to note that the introduction of extra variables also
  imposes extra constraints on the system - that each such extra variable be
  non-negative. This follows from the very definition of the variables
  themselves (i.e. they are absolute values to be either added or subtracted
  from the right hand side of the inequality).

  \;

  In our case, doing such a transformation proves extremely beneficial. Most
  importantly, it gives us a straightforward way to find values for variables
  by solving a system of equations rather than a raw system of nequalities.

  \;

  <\framed>
    <\algorithm>
      Let I be a set of inequalities. For any such inequality, let
      <math|\<Gamma\>> and <math|\<Delta\>> represent the left and right hand
      sides respectively, and let <math|\<Xi\>> represent the inequality
      sign. Further, let s be an arbitrary slack variable. We create the set
      E of equalities from I in the following way:

      <\render-code>
        <with|font-series|bold|function> remove_inequalities(<math|\<phi\>>:Term):[Term]:

        \ \ \ \ <with|font-series|bold|foreach> (<math|\<Gamma\>>
        <math|\<Xi\>> <math|\<Delta\>>) in <math|\<phi\>>:

        \ \ \ \ \ \ \ \ <with|font-series|bold|case> <math|\<Xi\>>:

        \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|<math|\<leq\>>> : add
        (<math|\<Gamma\>> + s <math|\<Xi\>> <math|\<Delta\>>) to E \ \ \ \ 

        \ \ \ \ \ \ \ \ \ \ \ \ <math|\<less\>> : add (<math|\<Gamma\>> + s +
        1 <math|\<Xi\>> <math|\<Delta\>>) to E

        \ \ \ \ \ \ \ \ \ \ \ \ <math|\<gtr\>> : add (<math|\<Gamma\>> - s -
        1 <math|\<Xi\>> <math|\<Delta\>>) to E

        \ \ \ \ \ \ \ \ \ \ \ \ <with|font-series|bold|<math|\<geqslant\>>> :
        add (<math|\<Gamma\>> - s <math|\<Xi\>> <math|\<Delta\>>) to E

        \ \ \ \ <with|font-series|bold|end case>

        <with|font-series|bold|end function>
      </render-code>
    </algorithm>
  </framed>

  <subsubsection|Simplifying the system>

  Having transformed our system of inequalities into an equivalent system of
  equations, we now proceed to simplify it. This procedure is simply a matter
  of putting each equation into <with|font-shape|italic|standard form>, and
  simplifying as far as possible //TODO.

  <subsubsection|Solving the system>

  The final step is to solve the simplified system of equations, in order to
  extract a final set of solutions for the variables involved. We do so by a
  structural analysis of the system, on the basis of which we then apply an
  appropriate heuristic (or set of heuristics) to minimize overall
  computation.

  \;

  <with|font-series|bold|System type>

  As mentioned, the system to solve can be either linear or polynomial in
  nature. From a mathematical perspective, linear systems are generally
  easier to solve, and there are several efficient algorithms available.
  Polynomial systems are not as succint, and will in our case require custom
  heuristics, which we discuss later.

  \;

  <with|font-series|bold|Linear systems>

  For any linear system of equations, it is true that it either:

  <\enumerate-numeric>
    <item>has no solutions, or

    <item>has one solution, or

    <item>has an infinite number of solutions
  </enumerate-numeric>

  \;

  Following the assumptions made for our algorithm, case 1 can never occur,
  and we would thus seemingly be left only to deal with single or infinite
  solutions. However, a linear system (generally) has a single solution if
  and only if it is <with|font-shape|italic|> contains at most as many
  variables as equations. Due to the introduction of extra variables in the
  process of eliminating inequalities, this <with|font-shape|italic|cannot>
  be the case, as there will always be n+m variables in a system of n
  equations and m variables, and m \<gtr\> 0 must hold for the system to be
  non-trivial.

  \;

  We are thus limited to the case where we have to solve systems with a
  <with|font-shape|italic|possibly> infinite solution space. Possibly, since
  we in our case have to take into account that our values are integers, and
  that our solution space is bounded by the inequalities involved<\footnote>
    In the system of equations constructed from these inequalities, these
    constraints are founf in the non-negative constraints on the extra
    variables introduced.
  </footnote>. Regardless of how the space looks, we can still device a
  method through which we find and return the first feasible solution
  available in it. This can be done incrementally depending on the shape of
  the system:

  <\itemize-dot>
    <item>If the system consists of a <with|font-series|bold|single
    equation>, we can rapidly solve it using coeficient-elimination, or
    euclides algorithm.

    <item>If the system consists of <with|font-series|bold|multiple
    equations>, we can use matrix reduction in order to reduce the system to
    a set of bound and free variables, from which we then extract a solution.
    </itemize-dot>

  \;

  <with|font-series|bold|single equations>

  Resolving a single equation can be done quickly if we can find a variable
  whose coeficient divides the constant in the equation. Given an equation
  <math|\<Gamma\>+mv=C><with|font-shape|italic|,> where
  <with|font-shape|italic|mv> is such a coeficient-variable pair (m being the
  coeficient, v the variable), <math|\<Gamma\>> is the remaining
  coeficient-variable pairs, and C is a constant, the solution is
  v=<math|<frac|C|m>>, and for all other variables v<rsub|i> <math|\<in\>>
  <math|\<Gamma\>>, v<rsub|i>=0.

  \;

  <\framed>
    <\example>
      \;

      \;

      Consider:\ 

      <\equation*>
        2x \<noplus\>+7y-z +s<rsub|1>=10
      </equation*>

      since 2 divides 10, let 2x be our mv pair. The solution to the equation
      thus becomes:

      <\equation*>
        <around*|{|x=5\<nocomma\>,y=0,z=0,s<rsub|1>=0|}>
      </equation*>

      We could also have picked 1<math|s<rsub|1>> as our mv pair, and arrived
      at the solution, and arrived at the solution:

      <\equation*>
        <around*|{|x=0\<nocomma\>,y=0,z=0,s<rsub|1>=10|}>
      </equation*>

      The same holds for z.
    </example>
  </framed>

  \;

  \;

  A useful corrolary of the above is that for all values of C
  <math|\<geqslant\>> 0, we can always perform this procedure due to the
  presence of the extra variable.\ 

  \;

  If C is negative, and there is no other mv pair to resolve the equation, we
  can instead make use of euclides algorithm in order to resolve it. //TODO

  \;

  <with|font-series|bold|System of equations>

  An underdetermined system of equations (which is what we will always deal
  with) can be solved using standard algebra, by reducing the system to a set
  of <with|font-shape|italic|bound> and <with|font-shape|italic|unbound>
  variables. Arbitrary values can then be assigned to the free variables, as
  these are free to vary, and the values of the bound variables can further
  be deduced by resubstitution.

  \;

  <\framed>
    <\example>
      \;

      \;

      Consider:\ 

      <\eqnarray*>
        <tformat|<table|<row|<cell|-x-2y+z+s<rsub|1>=1>|<cell|>|<cell|>>|<row|<cell|2x-y+s<rsub|2>=1>|<cell|>|<cell|>>>>
      </eqnarray*>

      \;

      Using the first row as pivot, we can isolate x as bound variable, and
      substitute it into the remaining two rows:\ 
    </example>

    <\eqnarray*>
      <tformat|<table|<row|<cell|x=-2y+s<rsub|1>-1>|<cell|>|<cell|>>|<row|<cell|-5y+2z+2s<rsub|1>+s<rsub|2>=3>|<cell|>|<cell|>>>>
    </eqnarray*>

    \;

    Finally, y is isolated as a bound variable from the second row in the
    same way:

    \;

    <\eqnarray*>
      <tformat|<table|<row|<cell|x=2y+s<rsub|1>-1>|<cell|>|<cell|>>|<row|<cell|y=<frac|2|5>z+<frac|2|5>s<rsub|1>+<frac|1|5>s<rsub|2>-<frac|3|5>>|<cell|>|<cell|>>>>
    </eqnarray*>

    \;

    \;

    Our unbound variables are hence z, <math|s<rsub|1>> and <math|s<rsub|2>>.
    Subject to the restrictions defined in our algorithm, we may assign them
    with arbitrary values, resulting in this case in an infinite number of
    solutions. One such solution is the trivial
    <math|<around*|{|y=-<frac|3|5>\<nocomma\>,x=<frac|1|5>,z=0,s<rsub|1>=0,s<rsub|2>=0|}>>.
  </framed>

  \;

  The obvious problem above is that neither x nor y are integers. While it
  <with|font-shape|italic|is> possible to device a complementary algorithm
  which solves for explicit integer solutions, this problem is NP-hard, and
  would in general add unacceptable overhead to our solving process.

  \;

  What we can do instead is to employ a technique used in linear programming
  known as <with|font-shape|italic|relaxation>. Here, the involved variables
  are solved for as if they were real numbers (as we did above), and then
  simply rounded off to become ``equivalent'' integers<\footnote>
    While this is known to complicate the process of finding an optimized
    solution in LP, it does no damage to us as we are only interested in an
    arbitrary solution. \ 
  </footnote>.\ 

  \;

  Relaxation enables us to rapidly find a solution, since it generally
  requires that the system be solved only once to find a satisfactory
  solution set. It has another, implicit benefit as well, which is that it
  allows us to easily extend the system to support floating point values as
  well, when such become supported in KeY.

  \;

  <\framed>
    <\algorithm>
      Let S = (E, V) be a system of equations, where E = [Eq<rsub|1>, ...
      ,Eq<rsub|n>] is the set of equations in the system, and V = [v<rsub|1>,
      ... , v<rsub|n>] is the set of variables in the system.

      \;

      Let E be an equation of the form V = C, where V is the set of variables
      in E and C is a constant. Further, let V = [m<rsub|1>v<rsub|1>,
      ...<math|> , m<rsub|n>v<rsub|n>], s.t. for the couple
      m<rsub|i>v<rsub|i>, v<rsub|i> is a variable, and m<rsub|i> is a
      multiplier for v<rsub|i>.

      \;

      We find concrete values for\ 
    </algorithm>
  </framed>

  <new-page*><section|Implementation>

  <new-page*><section|Discussion>

  <new-page*><section|Conclusion>

  <\bibliography|bib|tm-plain|keystone.bib>
    <\bib-list|5>
      <bibitem*|1><label|bib-KeY2005>Wolfgang<nbsp>Ahrendt, Thomas<nbsp>Baar,
      Bernhard<nbsp>Beckert, Richard<nbsp>Bubel, Martin<nbsp>Giese,
      Reiner<nbsp>Hähnle, Wolfram<nbsp>Menzel, Wojciech<nbsp>Mostowski,
      Andreas<nbsp>Roth, Steffen<nbsp>Schlager<localize| and >Peter
      H.<nbsp>Schmitt.<newblock> The KeY tool.<newblock>
      <with|font-shape|italic|Software and System Modeling>, 4:32--54,
      2005.<newblock>

      <bibitem*|2><label|bib-Beckert01>Bernhard<nbsp>Beckert.<newblock> A
      Dynamic Logic for the formal verification of Java Card
      programs.<newblock> <localize|In >I.<nbsp>Attali<localize| and
      >T.<nbsp>Jensen<localize|, editors>, <with|font-shape|italic|Java on
      Smart Cards: Programming and Security. Revised Papers, Java Card 2000,
      International Workshop, Cannes, France>, LNCS 2041, <localize|pages
      >6--24. Springer, 2001.<newblock>

      <bibitem*|3><label|bib-EngelHaehnle07>Christian<nbsp>Engel<localize|
      and >Reiner<nbsp>Hähnle.<newblock> Generating unit tests from formal
      proofs.<newblock> <localize|In >Bertrand<nbsp>Meyer<localize| and
      >Yuri<nbsp>Gurevich<localize|, editors>, <with|font-shape|italic|Proc.
      Tests and Proofs (TAP), Zürich, Switzerland>, lncs. Spv, to appear,
      2007.<newblock>

      <bibitem*|4><label|bib-Paganelli2010>Wolfgang Ahrendt<nbsp>Gabriele
      Paganelli.<newblock> Verification driven test generator.<newblock>
      <localize|In ><with|font-shape|italic|Publications of the CHARTER
      project>. 2010.<newblock>

      <bibitem*|5><label|bib-MLH07>Oleg<nbsp>Mürk,
      Daniel<nbsp>Larsson<localize| and >Reiner<nbsp>Hähnle.<newblock> KeY-C:
      a tool for verification of C programs.<newblock> <localize|In
      >Frank<nbsp>Pfenning<localize|, editor>, <with|font-shape|italic|Proc.
      21st Conference on Automated Deduction (CADE), Bremen, Germany>,
      <localize|volume> 4603<localize| of ><with|font-shape|italic|LNCS>,
      <localize|pages >385--390. Springer-Verlag, 2007.<newblock>
    </bib-list>
  </bibliography>
</body>

<\references>
  <\collection>
    <associate|auto-1|<tuple|1|3>>
    <associate|auto-10|<tuple|1.4.3|5>>
    <associate|auto-11|<tuple|1.5|5>>
    <associate|auto-12|<tuple|2|6>>
    <associate|auto-13|<tuple|2.1|6>>
    <associate|auto-14|<tuple|2.2|6>>
    <associate|auto-15|<tuple|2.3|6>>
    <associate|auto-16|<tuple|2.3.1|7>>
    <associate|auto-17|<tuple|2.3.2|8>>
    <associate|auto-18|<tuple|2.3.3|8>>
    <associate|auto-19|<tuple|2.3.4|9>>
    <associate|auto-2|<tuple|1.1|3>>
    <associate|auto-20|<tuple|3|9>>
    <associate|auto-21|<tuple|4|11>>
    <associate|auto-22|<tuple|5|12>>
    <associate|auto-23|<tuple|5|13>>
    <associate|auto-24|<tuple|5|13>>
    <associate|auto-3|<tuple|1.2|3>>
    <associate|auto-4|<tuple|1.3|4>>
    <associate|auto-5|<tuple|1.3.1|4>>
    <associate|auto-6|<tuple|1.3.2|4>>
    <associate|auto-7|<tuple|1.4|4>>
    <associate|auto-8|<tuple|1.4.1|5>>
    <associate|auto-9|<tuple|1.4.2|5>>
    <associate|bib-Beckert01|<tuple|2|13>>
    <associate|bib-EngelHaehnle07|<tuple|3|13>>
    <associate|bib-KeY2005|<tuple|1|13>>
    <associate|bib-MLH07|<tuple|5|13>>
    <associate|bib-Paganelli2010|<tuple|4|13>>
    <associate|footnote-1|<tuple|1|3>>
    <associate|footnote-10|<tuple|10|?>>
    <associate|footnote-2|<tuple|2|3>>
    <associate|footnote-3|<tuple|3|3>>
    <associate|footnote-4|<tuple|4|3>>
    <associate|footnote-5|<tuple|5|4>>
    <associate|footnote-6|<tuple|6|5>>
    <associate|footnote-7|<tuple|7|6>>
    <associate|footnote-8|<tuple|8|8>>
    <associate|footnote-9|<tuple|9|?>>
    <associate|footnr-1|<tuple|1|3>>
    <associate|footnr-10|<tuple|10|?>>
    <associate|footnr-2|<tuple|2|3>>
    <associate|footnr-3|<tuple|3|3>>
    <associate|footnr-4|<tuple|4|3>>
    <associate|footnr-5|<tuple|5|4>>
    <associate|footnr-6|<tuple|6|5>>
    <associate|footnr-7|<tuple|7|6>>
    <associate|footnr-8|<tuple|8|8>>
    <associate|footnr-9|<tuple|9|?>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|bib>
      KeY2005

      MLH07

      Beckert01

      EngelHaehnle07

      Paganelli2010
    </associate>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|1<space|2spc>Introduction>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|1.1<space|2spc>The KeY system
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2>>

      <with|par-left|<quote|1.5fn>|1.2<space|2spc>KeYTestGen2
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>>

      <with|par-left|<quote|1.5fn>|1.3<space|2spc>Test data generation in
      KeYTestGen2 <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4>>

      <with|par-left|<quote|3fn>|1.3.1<space|2spc>Object and boolean values
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>

      <with|par-left|<quote|3fn>|1.3.2<space|2spc>Numeric types
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6>>

      <with|par-left|<quote|1.5fn>|1.4<space|2spc>Performance issues
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7>>

      <with|par-left|<quote|3fn>|1.4.1<space|2spc>Execution time
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>>

      <with|par-left|<quote|3fn>|1.4.2<space|2spc>Memory usage
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-9>>

      <with|par-left|<quote|3fn>|1.4.3<space|2spc>Addressing performance
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10>>

      <with|par-left|<quote|1.5fn>|1.5<space|2spc>Contribution of this work
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|2<space|2spc>Design>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-12><vspace|0.5fn>

      <with|par-left|<quote|1.5fn>|2.1<space|2spc>Assumptions
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-13>>

      <with|par-left|<quote|1.5fn>|2.2<space|2spc>Branch-and-bound
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14>>

      <with|par-left|<quote|1.5fn>|2.3<space|2spc>Pre-processing
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-15>>

      <with|par-left|<quote|1.5fn>|2.4<space|2spc>Solving
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-16>>

      <with|par-left|<quote|3fn>|2.4.1<space|2spc>Basics
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-17>>

      <with|par-left|<quote|3fn>|2.4.2<space|2spc>Eliminating inequalities
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-18>>

      <with|par-left|<quote|3fn>|2.4.3<space|2spc>Simplifying the system
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-19>>

      <with|par-left|<quote|3fn>|2.4.4<space|2spc>Solving the system
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-20>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|3<space|2spc>Implementation>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-21><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|4<space|2spc>Discussion>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-22><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|5<space|2spc>Conclusion>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-23><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Bibliography>
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-24><vspace|0.5fn>
    </associate>
  </collection>
</auxiliary>