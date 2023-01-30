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
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.Contract;

public class MayUseMethodContractCondition extends VariableConditionAdapter {
    private final String parameter;

    public MayUseMethodContractCondition(String parameter) {
        this.parameter = parameter;
    }

    @Override
    public boolean check(SchemaVariable var,
                         SVSubstitute subst,
                         SVInstantiations svInst,
                         Services services) {

        Contract contract = services.getSpecificationRepository().getContractByName(parameter);
        return services.getProof().mgt().isContractApplicable(contract);
    }

    public String getParameter() {
        return parameter;
    }

    @Override
    public String toString () {
        return "\\mayUseMethodContract[\"" + parameter + "\"]";
    }

}
