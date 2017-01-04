package de.tud.cs.se.ds.psec.parser.ast;

import java.util.List;

import org.objectweb.asm.Label;
import org.objectweb.asm.MethodVisitor;

import de.tud.cs.se.ds.psec.compiler.ProgVarHelper;
import de.tud.cs.se.ds.psec.compiler.ast.RuleInstantiations;
import de.tud.cs.se.ds.psec.compiler.ast.TacletASTNode;
import de.tud.cs.se.ds.psec.util.UniqueLabelManager;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * Directive to store a global {@link Label}; either with a simple label name
 * like "l0" or with a complex {@link NameDecl} based on the name of a
 * {@link ProgramVariable}.
 *
 * @author Dominic Scheurer
 */
public class GlobalLabelInitialization extends Instruction {
    private LabelNameOrNameDecl labelName;

    /**
     * @param labelName
     */
    public GlobalLabelInitialization(String labelName) {
        this.labelName = new LabelNameOrNameDecl(labelName);
    }

    /**
     * 
     * @param nameDecl
     */
    public GlobalLabelInitialization(NameDecl nameDecl) {
        this.labelName = new LabelNameOrNameDecl(nameDecl);
    }

    @Override
    public void translate(MethodVisitor mv, ProgVarHelper pvHelper,
            UniqueLabelManager labelManager, RuleInstantiations instantiations,
            Services services, List<TacletASTNode> children) {
        
        registerGlobalLabel(labelName.getName(instantiations));

    }

}
