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

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import org.key_project.util.collection.ImmutableArray;


/**
 * ensures that the given instantiation for the schemavariable denotes a model method. For
 * determining the method the callee and the arguments of the method are needed as arguments.
 *
 * This is a pretty direct adaptation of {@link StaticMethodCondition}.
 *
 * @see StaticMethodCondition
 * @author Mattias Ulbrich 2022
 */
public final class ModelMethodCondition extends VariableConditionAdapter {

    private final boolean negation;
    private final SchemaVariable caller;
    private final SchemaVariable methname;
    private final SchemaVariable args;

    /**
     * Create a new instance of the variable condition.
     *
     * @param caller the receiver of the method call
     * @param methname name of the method
     * @param args arguments
     * @param negation iff the condition is to be negated
     */
    public ModelMethodCondition(SchemaVariable caller, SchemaVariable methname, SchemaVariable args, boolean negation) {
        this.negation = negation;
        this.caller = caller;
        this.methname = methname;
        this.args = args;
    }

    /**
     * Create a new instance of the variable condition. Without explicit receiver.
     *
     * @param methname name of the method
     * @param args arguments
     * @param negation iff the condition is to be negated
     */
    public ModelMethodCondition(SchemaVariable methname, SchemaVariable args, boolean negation) {
        this.negation = negation;
        this.caller = null;
        this.methname = methname;
        this.args = args;
    }

    private static ImmutableArray<Expression> toExpArray(ImmutableArray<? extends ProgramElement> a) {
        Expression[] result = new Expression[a.size()];
        for (int i=0; i<a.size(); i++) {
            result[i]=(Expression)a.get(i);
        }
        return new ImmutableArray<>(result);
    }


    @SuppressWarnings("unchecked")
    @Override
    public boolean check(SchemaVariable var, SVSubstitute subst,
                         SVInstantiations svInst, Services services) {

        ReferencePrefix rp = (ReferencePrefix) svInst.getInstantiation(caller);
        MethodName mn = (MethodName) svInst.getInstantiation(methname);
        ImmutableArray<ProgramElement> ape =
                (ImmutableArray<ProgramElement>) svInst.getInstantiation(args);

        if (rp != null && mn != null && ape != null) {
            ImmutableArray<Expression> ar
                    = toExpArray((ImmutableArray<ProgramElement>)svInst.getInstantiation(args));
            if (var == args) {
                ar = toExpArray((ImmutableArray<? extends ProgramElement>)subst);
            }
            ExecutionContext ec
                    = svInst.getContextInstantiation().activeStatementContext();
            MethodReference mr =new MethodReference(ar, mn, rp);
            KeYJavaType prefixType;
            // static vs. instance method
            if (rp instanceof Expression) {
                prefixType = services.getTypeConverter().getKeYJavaType((Expression) rp, ec);
            } else {
                assert rp instanceof TypeRef;
                prefixType = ((TypeRef)rp).getKeYJavaType();
            }
            IProgramMethod method;
            if (ec!=null) {
                method = mr.method(services, prefixType, ec);
                // we are only interested in the signature. The method
                // must be declared in the static context.
            } else { //no execution context
                method = mr.method (services, prefixType,
                        mr.getMethodSignature(services, ec),
                        prefixType);
            }
            if (method == null) {
                return false;
            }
            return negation ^ method.isModel();
        }
        return true;
    }


    @Override
    public String toString () {
        return (negation ? "\\not " : "") + "\\modelMethodReference(" + caller
                + ", " + methname + ", " + args + ")";
    }
}