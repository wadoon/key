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

package de.uka.ilkd.key.java.ast.statement;

import com.github.javaparser.ast.key.KeyTransactionStatement;
import de.uka.ilkd.key.java.ast.NameAbstractionTable;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceData;
import de.uka.ilkd.key.java.ast.SourceElement;
import de.uka.ilkd.key.java.ast.visitor.Visitor;
import de.uka.ilkd.key.rule.MatchConditions;

public class TransactionStatement extends JavaStatement {
    private final KeyTransactionStatement.TransactionType type;

    public TransactionStatement(int type) {
        this(KeyTransactionStatement.TransactionType.values()[type]);
    }

    public TransactionStatement(KeyTransactionStatement.TransactionType type) {
        super();
        this.type = type;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnTransactionStatement(this);
    }

    @Override
    public ProgramElement getChildAt(int index) {
        return null;
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    public void prettyPrint(de.uka.ilkd.key.java.PrettyPrinter p) throws java.io.IOException {
        p.printTransactionStatement(this);
    }

    public int getPrecedence() {
        return 13;
    }

    public String toString() {
        return type.symbol;
    }

    public boolean equals(Object o) {
        if (o != null && o instanceof TransactionStatement) {
            return ((TransactionStatement) o).type == this.type;
        }
        return false;
    }


    public MatchConditions match(SourceData source, MatchConditions conditions) {
        if (this.equals(source.getSource())) {
            source.next();
            return conditions;
        }
        return null;
    }

    public boolean equalsModRenaming(SourceElement source, NameAbstractionTable nat) {
        return this.equals(source);
    }


}