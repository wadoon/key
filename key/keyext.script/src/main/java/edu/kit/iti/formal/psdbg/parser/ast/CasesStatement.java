package edu.kit.iti.formal.psdbg.parser.ast;

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */


import edu.kit.iti.formal.psdbg.parser.ScriptLanguageParser;
import edu.kit.iti.formal.psdbg.parser.Visitor;
import lombok.*;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */
@Setter
@Getter
@RequiredArgsConstructor
public class CasesStatement extends Statement<ScriptLanguageParser.CasesStmtContext> {
    @NonNull
    private final List<CaseStatement> cases = new ArrayList<>();
    // @NonNull private Statements defaultCase = new Statements();
    @NonNull
    private DefaultCaseStatement defCaseStmt = new DefaultCaseStatement();

    @Override
    public ASTNode[] getChildren() {
        if (defCaseStmt == null)
            return (ASTNode[]) cases.toArray();
        else {
            val ret = new ASTNode[cases.size() + (defCaseStmt != null ? 1 : 0)];
            System.arraycopy(cases.toArray(), 0, ret, 0, cases.size());
            ret[ret.length - 1] = defCaseStmt;
            return ret;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public CasesStatement copy() {
        CasesStatement c = new CasesStatement();
        cases.forEach(caseStatement -> c.cases.add(caseStatement.copy()));
        //  if (defaultCase != null)
        //      c.defaultCase = defaultCase.copy();
        if (defCaseStmt != null)
            c.defCaseStmt = defCaseStmt.copy();
        c.setRuleContext(this.ruleContext);
        return c;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        CasesStatement that = (CasesStatement) o;

        for (int i = 0; i < cases.size(); i++) {
            if (!cases.get(i).eq(that.cases.get(i)))
                return false;
        }

        return getDefCaseStmt() != null ? getDefCaseStmt().eq(that.getDefCaseStmt()) : that.getDefCaseStmt() == null;
    }

}
