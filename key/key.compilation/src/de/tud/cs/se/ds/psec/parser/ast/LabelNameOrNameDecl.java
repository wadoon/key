package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.GlobalLabelHelper;
import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;

/**
 * A container class for either literal {@link Label} names or {@link NameDecl}
 * objects.
 *
 * @author Dominic Scheurer
 */
public class LabelNameOrNameDecl extends TranslationTacletASTElement {
    private String labelName = null;
    private NameDecl nameDecl = null;

    /**
     * @param labelName
     */
    public LabelNameOrNameDecl(String labelName) {
        this.labelName = labelName;
    }

    /**
     * @param nameDecl
     */
    public LabelNameOrNameDecl(NameDecl nameDecl) {
        this.nameDecl = nameDecl;
    }

    /**
     * Returns the stored {@link Label} name, possibly based on given
     * {@link RuleInstantiations} (if the encapsulated object is a
     * {@link NameDecl}).
     * 
     * @param instantiations
     *            The {@link RuleInstantiations} object for retrieving the name
     *            of a {@link NameDecl}.
     * @return The {@link Label} name.
     */
    public String getName(RuleInstantiations instantiations) {
        return !isExplicitName() ? nameDecl.getName(instantiations) : labelName;
    }

    /**
     * @return true iff the comprised label name is given explicitely as a
     *         {@link String} and not as a {@link NameDecl}.
     */
    public boolean isExplicitName() {
        return labelName != null;
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            GlobalLabelHelper globalLabelHelper, UniqueLabelManager labelManager,
            RuleInstantiations instantiations, Services services, List<TacletASTNode> children) {
        // This element should not be translated.
        // That's maybe a design flaw...
    }

}
