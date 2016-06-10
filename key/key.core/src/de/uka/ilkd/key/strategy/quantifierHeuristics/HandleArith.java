// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import org.key_project.common.core.logic.op.Function;
import org.key_project.common.core.logic.op.Junctor;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.util.LRUCache;
import org.key_project.util.collection.Pair;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.rule.metaconstruct.arith.Polynomial;

/**
 * This class is used to prove some simple arithmetic problem which are 
 * a==b, a>=b, a<=b; Besides it can be used to prove that a>=b or a<=b by 
 * knowing that c>=d or c<=d;
 *   
 */
public class HandleArith {
		
	private HandleArith() {}
    

	
	/**
     * try to prove atom by using polynomial
     * 
     * @param problem
     * @return <code>trueT</code> if if formu is proved to true,
     *         <code>falseT</code> if false, and <code>problem</code> if it
     *         cann't be proved.
     */
    public static JavaDLTerm provedByArith(JavaDLTerm problem, Services services) {
       final LRUCache<JavaDLTerm, JavaDLTerm> provedByArithCache = services.getCaches().getProvedByArithFstCache();
       JavaDLTerm result; 
       synchronized(provedByArithCache) { 
           result = provedByArithCache.get(problem);
       }
       if (result != null) {
          return result;
       }
       
       TermBuilder tb = services.getTermBuilder();
       IntegerLDT integerLDT = services.getTheories().getIntegerLDT();
       
       final JavaDLTerm trueT = tb.tt(); 
       final JavaDLTerm falseT = tb.ff(); 

       final JavaDLTerm arithTerm = formatArithTerm ( problem, tb, integerLDT, services.getCaches());
       if ( arithTerm.equals ( falseT ) ) {
          result = provedArithEqual ( problem, tb, services );
          putInTermCache(provedByArithCache, problem, result);
          return result;
       }
        Polynomial poly1 = Polynomial.create ( arithTerm.sub ( 0 ), services );
        Polynomial poly2 = Polynomial.create ( arithTerm.sub ( 1 ), services );

        if ( poly2.valueLeq ( poly1 ) ) {
            putInTermCache(provedByArithCache, problem, trueT);
            return trueT;
        }
        if ( poly1.valueLess ( poly2 ) ) {
            putInTermCache(provedByArithCache, problem, falseT);
            return falseT;
        }
        putInTermCache(provedByArithCache, problem, problem);
        return problem;
    }



    private static void putInTermCache(final LRUCache<JavaDLTerm, JavaDLTerm> provedByArithCache, 
            final JavaDLTerm key, final JavaDLTerm value) {
        synchronized(provedByArithCache) { 
            provedByArithCache.put(key, value);
        }
    }
        
    /**
     * @param problem
     * @return true if atom.sub(0) is euqual to atom.sub(1), false if not
     *         equal, else return atom
     */
    private static JavaDLTerm provedArithEqual(JavaDLTerm problem, TermBuilder tb, Services services) {
       final JavaDLTerm trueT = tb.tt(); 
       final JavaDLTerm falseT = tb.ff(); 

        boolean temp = true;
        JavaDLTerm pro = problem;
        Operator op = pro.op ();
        // may be here we should check wehre sub0 and sub1 is integer.
        while ( op == Junctor.NOT ) {
            pro = pro.sub ( 0 );
            op = pro.op ();
            temp = !temp;
        }
        if ( op == Equality.EQUALS ) {
            JavaDLTerm sub0 = pro.sub ( 0 );
            JavaDLTerm sub1 = pro.sub ( 1 );
            Polynomial poly1 = Polynomial.create ( sub0, services );
            Polynomial poly2 = Polynomial.create ( sub1, services );
            boolean gt = poly2.valueLeq ( poly1 );
            boolean lt = poly1.valueLeq ( poly2 );
            if ( gt && lt ) return temp ? trueT : falseT;
            if ( gt || lt ) return temp ? falseT : trueT;
        }
        return problem;
    }
    

    /**
     * Try to prove problem by know that axiom is true. The idea is that we
     * know a>=b(axiom),we want to prove c>=d(problem). It is enough to
     * prove that c+b>=a+d which means c>=d is true. or we prove that
     * !(c>=d) which is d>=c+1 is true. This means c>= d is false;
     * 
     * @param problem
     * @param axiom
     * @return trueT if true, falseT if false, and atom if can't be prove;
     */
    public static JavaDLTerm provedByArith(JavaDLTerm problem, JavaDLTerm axiom, Services services) {
        final Pair<JavaDLTerm, JavaDLTerm> key = new Pair<JavaDLTerm, JavaDLTerm>(problem, axiom);
        final LRUCache<Pair<JavaDLTerm, JavaDLTerm>, JavaDLTerm> provedByArithCache = 
              services.getCaches().getProvedByArithSndCache();
        JavaDLTerm result; 
        synchronized (provedByArithCache) {
            result = provedByArithCache.get(key);   
        }
        if (result != null) {
           return result;
        }
       
        final TermBuilder tb = services.getTermBuilder();
        final IntegerLDT integerLDT = services.getTheories().getIntegerLDT();
        final ServiceCaches caches = services.getCaches();
        
        final JavaDLTerm cd = formatArithTerm ( problem, tb, integerLDT, caches );
        final JavaDLTerm ab = formatArithTerm ( axiom, tb, integerLDT, caches );
        final JavaDLTerm trueT = tb.tt(); 
        final JavaDLTerm falseT = tb.ff(); 

        if ( cd.op() == Junctor.FALSE || ab.op() == Junctor.FALSE ) {
            synchronized (provedByArithCache) {
                provedByArithCache.put(key, problem);
            }
           return problem;
        }
        Function addfun = integerLDT.getAdd();
        JavaDLTerm arithTerm = tb.geq ( tb.func ( addfun, cd.sub ( 0 ), ab.sub ( 1 ) ),
                                  tb.func ( addfun, ab.sub ( 0 ), cd.sub ( 1 ) ) );
        JavaDLTerm res = provedByArith ( arithTerm, services );
        if ( res.op() == Junctor.TRUE ) {
            synchronized (provedByArithCache) {
                provedByArithCache.put(key, trueT);
            }
           return trueT;
        }
        JavaDLTerm t0 = formatArithTerm ( tb.not ( problem ), tb, integerLDT, caches );
        arithTerm = tb.geq ( tb.func ( addfun, t0.sub ( 0 ), ab.sub ( 1 ) ),
                             tb.func ( addfun, ab.sub ( 0 ), t0.sub ( 1 ) ) );
        res = provedByArith ( arithTerm, services );
        if ( res.op() == Junctor.TRUE ) {
            synchronized (provedByArithCache) {
                provedByArithCache.put(key, falseT);
            }
           return falseT;
        }
        synchronized (provedByArithCache) {
            provedByArithCache.put(key, problem);
        }
        return problem;
    }

    
    /**
     * Format literal to a form of "geq",linke a>=b;For example, a <=b to
     * b>=a;a>b to a>=b+1;!(a>=b) to b>=a+1..
     * 
     * @param problem
     * @return falseT if <code>term</code>'s operator is not >= or <=
     */
    private static JavaDLTerm formatArithTerm(final JavaDLTerm problem, TermBuilder tb, IntegerLDT ig, ServiceCaches caches) {
       final LRUCache<JavaDLTerm, JavaDLTerm> formattedTermCache = caches.getFormattedTermCache();
       JavaDLTerm pro; 
       synchronized (formattedTermCache) {
           pro = formattedTermCache.get(problem); 
       }
       if (pro != null) {
          return pro;
       }
       
        pro = problem;
        Operator op = pro.op ();
        boolean opNot = false;
        while ( op == Junctor.NOT ) {
            opNot = !opNot;
            pro = pro.sub ( 0 );
            op = pro.op ();
        }
        final Function geq = ig.getGreaterOrEquals ();
        final Function leq = ig.getLessOrEquals ();
        final JavaDLTerm falseT = tb.ff(); 

        if ( op == geq ) {
            if ( opNot )
                        pro = tb.geq ( pro.sub ( 1 ),
                                       tb.func ( ig.getAdd(),
                                                 pro.sub ( 0 ),
                                                 ig.one() ) );
        } else {
            if ( op == leq ) {
                if ( opNot )
                    pro = tb.geq ( pro.sub ( 0 ),
                                   tb.func ( ig.getAdd (),
                                             pro.sub ( 1 ),
                                             ig.one() ) );
                else
                    pro = tb.geq ( pro.sub ( 1 ), pro.sub ( 0 ) );
            } else
                pro = falseT;
        }
        
        putInTermCache(formattedTermCache, problem, pro);
        return pro;
    }
    
}