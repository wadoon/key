package recoder.kit.transformation.java5to4;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.ClassType;
import recoder.abstraction.Type;
import recoder.convenience.Naming;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.Import;
import recoder.java.ProgramElement;
import recoder.java.reference.*;
import recoder.kit.MiscKit;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.UnitKit;
import recoder.list.generic.ASTList;

import java.util.ArrayList;
import java.util.List;

public class RemoveStaticImports extends TwoPassTransformation {
    private final CompilationUnit cu;

    private List<Item> hotSpots;

    private List<Import> statics;

    public RemoveStaticImports(CrossReferenceServiceConfiguration sc, CompilationUnit cu) {
        super(sc);
        this.cu = cu;
    }

    public ProblemReport analyze() {
        this.hotSpots = new ArrayList<Item>();
        this.statics = new ArrayList<Import>();
        ASTList<Import> aSTList = this.cu.getImports();
        if (aSTList == null || aSTList.isEmpty())
            return IDENTITY;
        for (int i = 0, s = aSTList.size(); i < s; i++) {
            Import im = aSTList.get(i);
            if (im.isStaticImport())
                this.statics.add(im);
        }
        if (this.statics.isEmpty())
            return IDENTITY;
        TreeWalker tw = new TreeWalker(this.cu);
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            if (pe instanceof MemberReference && pe instanceof ReferenceSuffix && pe instanceof NameReference) {
                ClassType targetCT;
                MemberReference r = (MemberReference) pe;
                ReferenceSuffix referenceSuffix = (ReferenceSuffix) pe;
                NameReference nr = (NameReference) pe;
                if (referenceSuffix.getReferencePrefix() != null)
                    continue;
                if (r instanceof MethodReference) {
                    targetCT = getSourceInfo().getMethod((MethodReference) r).getContainingClassType();
                } else if (r instanceof FieldReference) {
                    targetCT = getSourceInfo().getField((FieldReference) r).getContainingClassType();
                } else if (r instanceof TypeReference) {
                    Type t = getSourceInfo().getType((TypeReference) r);
                    if (!(t instanceof ClassType))
                        continue;
                    targetCT = (ClassType) t;
                } else {
                    continue;
                }
                if (targetCT instanceof recoder.java.declaration.TypeDeclaration && UnitKit.getCompilationUnit((ProgramElement) targetCT) == this.cu)
                    continue;
                String n = nr.getName();
                for (int j = 0, si = this.statics.size(); j < si; j++) {
                    Import im = this.statics.get(j);
                    TypeReference tr = im.getTypeReference();
                    if (getSourceInfo().getType(tr) != targetCT)
                        continue;
                    if (!im.isMultiImport())
                        if (!n.equals(im.getStaticIdentifier().getText()))
                            continue;
                    TypeReference prefix = im.getTypeReference();
                    this.hotSpots.add(new Item(nr, prefix));
                }
            }
        }
        return super.analyze();
    }

    public void transform() {
        super.transform();
        for (Import i : this.statics)
            detach(i);
        for (Item hs : this.hotSpots) {
            String x = Naming.toPathName(hs.prefix, hs.r.getName());
            if (x.startsWith("java.lang."))
                x = x.substring(10);
            replace(hs.r, MiscKit.createUncollatedReferenceQualifier(getProgramFactory(), x));
        }
    }

    private static class Item {
        NameReference r;

        TypeReference prefix;

        Item(NameReference r, TypeReference prefix) {
            this.r = r;
            this.prefix = prefix;
        }
    }
}
