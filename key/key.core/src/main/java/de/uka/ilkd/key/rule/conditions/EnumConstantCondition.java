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


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.EnumClassDeclaration;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * ensures that the given instantiation for the schemavariable denotes a
 * constant of an enum type.
 * 
 * @author mulbrich
 * @since 2006-12-04
 * @version 2006-12-11
 */
public final class EnumConstantCondition extends VariableConditionAdapter {

    private final SchemaVariable reference;

    /**
     * the static reference condition checks if a suggested
     * instantiation for a schema variable denotes a reference to 
     * an enum constant.
     */
    public EnumConstantCondition (SchemaVariable reference) {
	this.reference = reference;
    }

    /**
     * Given a select term of the form {@code E::select(heap, null, E::$name} for
     * en enum {@code E} and an enum constant {@code name} within, extract the
     * program variable representing that field in the class
     *
     * @param term a selection term of the above kind.
     * @param services services to lookup things
     * @return {@code null} if this is not a term of this kind (or not a constant),
     *      the corresponding program variable otherwise.
     */
    public static ProgramVariable extractEnumProgramVar(Term term, Services services) {
        HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        if(heapLDT.isSelectOp(term.op())) {
            Term fieldTerm = term.sub(2);
            Operator fieldOp = fieldTerm.op();
            if (fieldOp instanceof Function) {
                String name = ((Function) fieldOp).name().toString();
                int split = name.indexOf("::$");
                if (split >= 0) {
                    ProgramVariable progvar = services.getJavaInfo()
                            .getAttribute(name.substring(split + 3),
                                    name.substring(0, split));
                    return progvar;
                }
            }
        }

        return null;
    }

    @Override
    public boolean check(SchemaVariable var, 
			 SVSubstitute subst, 
			 SVInstantiations svInst,
			 Services services) {

        if (var == reference) {
            Term term = (Term) subst;
            ProgramVariable progvar = extractEnumProgramVar(term, services);
            if (progvar != null) {
                return EnumClassDeclaration.isEnumConstant(progvar);
            } else {
                return false;
            }
        }
        return true;
    }

    
    @Override    
    public String toString () {
	return "\\enumConstant(" + reference + ")";
    }
}