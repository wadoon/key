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

import org.key_project.common.core.logic.op.Junctor;
import org.key_project.common.core.logic.op.Operator;
import org.key_project.common.core.logic.op.QuantifiableVariable;
import org.key_project.common.core.logic.op.Quantifier;

import de.uka.ilkd.key.logic.JavaDLTerm;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.Equality;

public class QuanEliminationAnalyser {
    
    /**
     * 
     * @param definition
     * @return the distance to the quantifier that can be eliminated;
     *         <code>Integer.MAX_VALUE</code> if the subformula is not an
     *         eliminable definition
     */
    public int eliminableDefinition(JavaDLTerm definition, PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> envPIO) {
        final PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> matrixPIO = walkUpMatrix ( envPIO );
        final JavaDLTerm matrix = matrixPIO.subTerm ();

        if ( matrixPIO.isTopLevel () ) return Integer.MAX_VALUE;
        
        PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> quantPIO = matrixPIO.up ();
        JavaDLTerm quantTerm = quantPIO.subTerm ();
        final boolean ex;
        if ( quantTerm.op () == Quantifier.EX ) {
            ex = true;
        } else if ( quantTerm.op () == Quantifier.ALL ) {
            ex = false;
        } else {
            return Integer.MAX_VALUE;
        }
        
        if ( !isDefinitionCandidate ( definition, envPIO.subTerm (), ex ) )
            return Integer.MAX_VALUE;

        int distance = 0;        
        while ( true ) {
            final QuantifiableVariable var =
                quantTerm.varsBoundHere ( 0 ).last ();

            if ( isDefinition ( definition, var, ex )
                 && isEliminableVariableSomePaths ( var, matrix, ex ) )
                return distance;

            if ( quantPIO.isTopLevel () ) return Integer.MAX_VALUE;
            quantPIO = quantPIO.up ();
            quantTerm = quantPIO.subTerm ();
            
            if ( quantTerm.op () != ( ex ? Quantifier.EX : Quantifier.ALL ) )
                return Integer.MAX_VALUE;
            
            ++distance;
        }
    }

    private boolean isDefinitionCandidate(JavaDLTerm t, JavaDLTerm env, boolean ex) {
        if ( !hasDefinitionShape ( t, ex ) ) return false;
        return !ex || !isBelowOr ( t, env );
    }

    private boolean isBelowOr(JavaDLTerm t, JavaDLTerm env) {
        final Operator envOp = env.op ();
        if ( envOp == Junctor.OR && ( env.sub ( 0 ) == t || env.sub ( 1 ) == t ) )
            return true;
        if ( envOp == Junctor.OR || envOp == Junctor.AND )
            return isBelowOr ( t, env.sub ( 0 ) )
                   || isBelowOr ( t, env.sub ( 1 ) );
        return false;
    }
    
    private boolean hasDefinitionShape(JavaDLTerm t, boolean ex) {
        for (QuantifiableVariable quantifiableVariable : t.freeVars()) {
            if (isDefinition(t, quantifiableVariable, ex)) return true;
        }
        return false;
    }
    
    private PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> walkUpMatrix(PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> pio) {
        while ( !pio.isTopLevel () ) {
            final PosInOccurrence<JavaDLTerm, SequentFormula<JavaDLTerm>> parent = pio.up ();
            final Operator parentOp = parent.subTerm ().op ();
            if ( parentOp != Junctor.AND && parentOp != Junctor.OR ) return pio;
            pio = parent;
        }
        return pio;
    }

    /**
     * The variable <code>var</code> is either eliminable or does not occur on
     * all conjunctive/disjunctive paths through <code>matrix</code>
     * (depending on whether <code>ex</code> is true/false)
     */
    public boolean isEliminableVariableSomePaths(QuantifiableVariable var,
                                                 JavaDLTerm matrix,
                                                 boolean ex) {
        if ( !matrix.freeVars ().contains ( var ) ) return true;
        
        final Operator op = matrix.op ();

        if ( op == ( ex ? Junctor.OR : Junctor.AND ) ) {
            return isEliminableVariableSomePaths ( var, matrix.sub ( 0 ), ex )
                   && isEliminableVariableSomePaths ( var, matrix.sub ( 1 ), ex );
        } else if ( op == ( ex ? Junctor.AND : Junctor.OR ) ) {
            return
            isEliminableVariableAllPaths ( var, matrix.sub ( 0 ), ex )
             || isEliminableVariableAllPaths ( var, matrix.sub ( 1 ), ex )
             || ( isEliminableVariableSomePaths ( var, matrix.sub ( 0 ), ex )
                  && isEliminableVariableSomePaths ( var, matrix.sub ( 1 ), ex ) );
        }

        if ( ex )
            return isDefiningEquationEx ( matrix, var );
        else
            return isDefiningEquationAll ( matrix, var );
    }
    
    /**
     * The variable <code>var</code> is eliminable on all
     * conjunctive/disjunctive paths through <code>matrix</code> (depending on
     * whether <code>ex</code> is true/false)
     */
    public boolean isEliminableVariableAllPaths(QuantifiableVariable var,
                                                JavaDLTerm matrix,
                                                boolean ex) {
        final Operator op = matrix.op ();

        if ( op == ( ex ? Junctor.OR : Junctor.AND ) ) {
            return isEliminableVariableAllPaths ( var, matrix.sub ( 0 ), ex )
                   && isEliminableVariableAllPaths ( var, matrix.sub ( 1 ), ex );
        } else if ( op == ( ex ? Junctor.AND : Junctor.OR ) ) {
            return isEliminableVariableAllPaths ( var, matrix.sub ( 0 ), ex )
                   || isEliminableVariableAllPaths ( var, matrix.sub ( 1 ), ex );
        }

        if ( ex )
            return isDefiningEquationEx ( matrix, var );
        else
            return isDefiningEquationAll ( matrix, var );
    }
    
    private boolean isDefinition(JavaDLTerm t, QuantifiableVariable var, boolean ex) {
        if ( ex )
            return isDefinitionEx ( t, var );
        else
            return isDefiningEquationAll ( t, var );
    }
    
    private boolean isDefinitionEx(JavaDLTerm t, QuantifiableVariable var) {
        if ( t.op () == Junctor.OR ) {
            return isDefinitionEx ( t.sub ( 0 ), var )
                   && isDefinitionEx ( t.sub ( 1 ), var );
        }
        return isDefiningEquationEx ( t, var );
    }
    
    private boolean isDefiningEquationAll(JavaDLTerm t, QuantifiableVariable var) {
        if ( t.op () != Junctor.NOT ) return false;
        return isDefiningEquation ( t.sub ( 0 ), var );
    }

    private boolean isDefiningEquationEx(JavaDLTerm t, QuantifiableVariable var) {
        return isDefiningEquation ( t, var );
    }

    private boolean isDefiningEquation(JavaDLTerm t, QuantifiableVariable var) {
        if ( t.op () != Equality.EQUALS ) return false;
        final JavaDLTerm left = t.sub ( 0 );
        final JavaDLTerm right = t.sub ( 1 );
        final Operator leftOp = left.op ();
        final Operator rightOp = right.op ();
        return leftOp == var && !right.freeVars ().contains ( var )
               || rightOp == var && !left.freeVars ().contains ( var );
    }
    
}