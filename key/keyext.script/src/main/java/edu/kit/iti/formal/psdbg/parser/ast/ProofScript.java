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

import java.util.Objects;

/**
 * @author Alexander Weigl
 * @version 1 (27.04.17)
 */
@Data
@EqualsAndHashCode(callSuper = false)
public class ProofScript extends ASTNode<ScriptLanguageParser.ScriptContext> {
    @NonNull
    @Getter
    @Setter
    private String name = "_";
    private Signature signature = new Signature();
    private Statements body = new Statements();

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public ProofScript copy() {
        ProofScript ps = new ProofScript();
        ps.setName(getName());
        ps.setBody(body.copy());
        ps.setSignature(signature.copy());
        ps.setRuleContext(this.ruleContext);
        return ps;
    }

    @Override
    public ASTNode[] getChildren() {
        return new ASTNode[]{getSignature(), getBody()};
    }

    @Override
    public boolean eq(ASTNode o) {
        if (this == o) return true;
        if (!(o instanceof ProofScript)) return false;
        if (!super.equals(o)) return false;

        ProofScript that = (ProofScript) o;

        if (getName() != null ? !getName().equals(that.getName()) : that.getName() != null) return false;
        if (getSignature() != null ? !getSignature().eq(that.getSignature()) : that.getSignature() != null)
            return false;
        return getBody() != null ? getBody().eq(that.getBody()) : that.getBody() == null;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;
        ProofScript that = (ProofScript) o;
        return Objects.equals(getName(), that.getName()) &&
                Objects.equals(getSignature(), that.getSignature()) &&
                Objects.equals(getBody(), that.getBody());
    }

    @Override
    public int hashCode() {
        return Objects.hash(super.hashCode(), getName(), getSignature(), getBody());
    }
}
