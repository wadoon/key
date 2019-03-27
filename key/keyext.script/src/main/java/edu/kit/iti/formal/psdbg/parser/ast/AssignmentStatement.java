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
import edu.kit.iti.formal.psdbg.parser.types.Type;
import lombok.*;

/**
 * An {@link AssignmentStatement} encapsulate the assigned variable
 * {@link AssignmentStatement#getLhs()} and an expression {@link AssignmentStatement#getRhs()}.
 *
 * @author Alexander Weigl
 * @version 1 (28.04.17)
 */

@ToString(includeFieldNames = true)
@NoArgsConstructor
@RequiredArgsConstructor()
@AllArgsConstructor
@Getter
@Setter
public class AssignmentStatement
        extends Statement<ScriptLanguageParser.AssignmentContext> {
    @NonNull
    private Variable lhs;

    private Expression rhs;

    private Type type;

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public AssignmentStatement copy() {
        AssignmentStatement s = new AssignmentStatement();
        s.lhs = lhs.copy();
        s.rhs = rhs.copy();
        s.type = type;
        s.setRuleContext(this.ruleContext);
        return s;
    }

    /**
     * Returns true, iff this assignment declares the assigned variable.
     */
    public boolean isDeclaration() {
        return type != null;
    }

    @Override
    public ASTNode[] getChildren() {
        return new ASTNode[]{getLhs(), getRhs()};
    }

    @Override
    public boolean eq(ASTNode o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        AssignmentStatement that = (AssignmentStatement) o;

        if (!getLhs().eq(that.getLhs())) return false;
        if (!getRhs().eq(that.getRhs())) return false;
        return getType() != null ? getType().equals(that.getType()) : that.getType() == null;
    }
}
