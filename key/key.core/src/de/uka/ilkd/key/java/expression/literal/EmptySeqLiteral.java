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

package de.uka.ilkd.key.java.expression.literal;

import org.key_project.common.core.logic.Name;
import org.key_project.common.core.program.GenericNameAbstractionTable;

import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.ldt.SeqLDT;



public class EmptySeqLiteral extends Literal {

    public static final EmptySeqLiteral INSTANCE = new EmptySeqLiteral();
    
    private EmptySeqLiteral() {}   
    
    
    @Override
    public boolean equalsModRenaming(SourceElement o, 
                                     GenericNameAbstractionTable nat) {
	return o == this;
    }


    public void visit(Visitor v) {
	v.performActionOnEmptySeqLiteral(this);
    }

    public void prettyPrint(PrettyPrinter p) throws java.io.IOException {
        p.printEmptySeqLiteral(this);
    }


    public KeYJavaType getKeYJavaType(Services javaServ) {
	return javaServ.getProgramServices().getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_SEQ);
    }

    @Override
    public Name getLDTName() {
        return SeqLDT.NAME;
    }
}
