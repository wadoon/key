package recoder.kit.transformation.java5to4;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ProgramFactory;
import recoder.abstraction.Type;
import recoder.convenience.TreeWalker;
import recoder.java.NonTerminalProgramElement;
import recoder.java.ProgramElement;
import recoder.java.declaration.*;
import recoder.java.reference.TypeReference;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

import java.util.ArrayList;
import java.util.List;

public class RemoveAnnotations extends TwoPassTransformation {
    private final NonTerminalProgramElement root;

    private List<AnnotationUseSpecification> toRemove;

    private List<AnnotationDeclaration> unusedAnnotationTypes;

    private List<AnnotationDeclaration> usedAnnotationTypes;

    public RemoveAnnotations(CrossReferenceServiceConfiguration sc, NonTerminalProgramElement root) {
        super(sc);
        this.root = root;
    }

    public ProblemReport analyze() {
        this.toRemove = new ArrayList<AnnotationUseSpecification>(100);
        this.unusedAnnotationTypes = new ArrayList<AnnotationDeclaration>(10);
        this.usedAnnotationTypes = new ArrayList<AnnotationDeclaration>(10);
        TreeWalker tw = new TreeWalker(this.root);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof AnnotationUseSpecification) {
                this.toRemove.add((AnnotationUseSpecification) pe);
                continue;
            }
            if (pe instanceof AnnotationDeclaration) {
                AnnotationDeclaration ad = (AnnotationDeclaration) pe;
                List<TypeReference> trl = getServiceConfiguration().getCrossReferenceSourceInfo().getReferences(ad);
                boolean remove = true;
                int i;
                for (i = 0; i < trl.size(); i++) {
                    if (!(trl.get(i).getASTParent() instanceof AnnotationUseSpecification)) {
                        remove = false;
                        break;
                    }
                }
                for (i = 0; i < ad.getMembers().size(); i++) {
                    MemberDeclaration md = ad.getMembers().get(i);
                    if (md instanceof recoder.java.declaration.TypeDeclaration) {
                        remove = false;
                        break;
                    }
                }
                if (remove) {
                    this.unusedAnnotationTypes.add(ad);
                    continue;
                }
                this.usedAnnotationTypes.add(ad);
            }
        }
        return super.analyze();
    }

    public void transform() {
        super.transform();
        for (AnnotationUseSpecification au : this.toRemove)
            detach(au);
        for (AnnotationDeclaration ad : this.unusedAnnotationTypes)
            detach(ad);
        for (AnnotationDeclaration ad : this.usedAnnotationTypes)
            replace(ad, makeInterface(ad));
    }

    private InterfaceDeclaration makeInterface(AnnotationDeclaration ad) {
        ProgramFactory f = getProgramFactory();
        InterfaceDeclaration replacement = getProgramFactory().createInterfaceDeclaration();
        ASTList<MemberDeclaration> oldMems = ad.getMembers();
        ASTArrayList aSTArrayList = new ASTArrayList(oldMems.size());
        for (int i = 0; i < oldMems.size(); i++) {
            MemberDeclaration newMD, md = oldMems.get(i);
            if (md instanceof AnnotationPropertyDeclaration) {
                AnnotationPropertyDeclaration apd = (AnnotationPropertyDeclaration) md;
                MethodDeclaration m = f.createMethodDeclaration();
                if (apd.getComments() != null)
                    m.setComments(apd.getComments().deepClone());
                m.setIdentifier(apd.getIdentifier().deepClone());
                m.setTypeReference(apd.getTypeReference().deepClone());
                MethodDeclaration methodDeclaration1 = m;
            } else if (md instanceof AnnotationDeclaration) {
                InterfaceDeclaration interfaceDeclaration = makeInterface((AnnotationDeclaration) md);
            } else {
                newMD = (MemberDeclaration) md.deepClone();
            }
            newMD.makeParentRoleValid();
            aSTArrayList.add(newMD);
        }
        replacement.setIdentifier(ad.getIdentifier().deepClone());
        replacement.setMembers(aSTArrayList);
        if (ad.getComments() != null)
            replacement.setComments(ad.getComments().deepClone());
        replacement.setDeclarationSpecifiers(ad.getDeclarationSpecifiers().deepClone());
        replacement.makeParentRoleValid();
        return replacement;
    }
}
