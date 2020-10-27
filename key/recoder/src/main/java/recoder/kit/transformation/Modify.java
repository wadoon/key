package recoder.kit.transformation;

import recoder.CrossReferenceServiceConfiguration;
import recoder.java.Declaration;
import recoder.java.ProgramElement;
import recoder.java.declaration.DeclarationSpecifier;
import recoder.java.declaration.Modifier;
import recoder.java.declaration.modifier.Static;
import recoder.kit.ModifierKit;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.list.generic.ASTList;

public class Modify extends TwoPassTransformation {
    private final boolean isVisible;

    private final int modifier;

    private final Declaration decl;

    private int insertPosition = -1;

    private Modifier remove;

    private Modifier insert;

    public Modify(CrossReferenceServiceConfiguration sc, boolean isVisible, Declaration decl, int code) {
        super(sc);
        if (decl == null)
            throw new IllegalArgumentException("Missing declaration");
        this.isVisible = isVisible;
        this.decl = decl;
        this.modifier = code;
    }

    private static boolean containsModifier(Declaration decl, Class mod) {
        ASTList<DeclarationSpecifier> aSTList = decl.getDeclarationSpecifiers();
        if (aSTList == null)
            return false;
        for (int i = 0; i < aSTList.size(); i++) {
            DeclarationSpecifier res = aSTList.get(i);
            if (mod.isInstance(res))
                return true;
        }
        return false;
    }

    public boolean isVisible() {
        return this.isVisible;
    }

    private int getLastModifierPosition() {
        ASTList aSTList = this.decl.getDeclarationSpecifiers();
        if (aSTList == null)
            return 0;
        return aSTList.size();
    }

    public ProblemReport analyze() {
        this.insertPosition = 0;
        Modifier mod = ModifierKit.createModifier(getProgramFactory(), this.modifier);
        if (this.modifier != 512 && containsModifier(this.decl, mod.getClass()))
            return setProblemReport(IDENTITY);
        switch (this.modifier) {
            case 512:
                this.remove = ModifierKit.getVisibilityModifier(this.decl);
                return setProblemReport(NO_PROBLEM);
            case 1:
                this.remove = ModifierKit.getVisibilityModifier(this.decl);
                if (!(this.remove instanceof recoder.java.declaration.modifier.Public))
                    this.insert = getProgramFactory().createPublic();
                return setProblemReport(NO_PROBLEM);
            case 4:
                this.remove = ModifierKit.getVisibilityModifier(this.decl);
                if (!(this.remove instanceof recoder.java.declaration.modifier.Protected))
                    this.insert = getProgramFactory().createProtected();
                return setProblemReport(NO_PROBLEM);
            case 2:
                this.remove = ModifierKit.getVisibilityModifier(this.decl);
                if (!(this.remove instanceof recoder.java.declaration.modifier.Private))
                    this.insert = getProgramFactory().createPrivate();
                return setProblemReport(NO_PROBLEM);
            case 8:
                if (ModifierKit.getVisibilityModifier(this.decl) != null)
                    this.insertPosition++;
                this.insert = getProgramFactory().createStatic();
                return setProblemReport(NO_PROBLEM);
            case 16:
                if (ModifierKit.getVisibilityModifier(this.decl) != null)
                    this.insertPosition++;
                if (containsModifier(this.decl, Static.class))
                    this.insertPosition++;
                this.insert = getProgramFactory().createFinal();
                return setProblemReport(NO_PROBLEM);
            case 1024:
                if (ModifierKit.getVisibilityModifier(this.decl) != null)
                    this.insertPosition++;
                this.insert = getProgramFactory().createAbstract();
                return setProblemReport(NO_PROBLEM);
            case 32:
                this.insertPosition = getLastModifierPosition();
                this.insert = getProgramFactory().createSynchronized();
                return setProblemReport(NO_PROBLEM);
            case 128:
                this.insertPosition = getLastModifierPosition();
                this.insert = getProgramFactory().createTransient();
                return setProblemReport(NO_PROBLEM);
            case 2048:
                this.insertPosition = getLastModifierPosition();
                this.insert = getProgramFactory().createStrictFp();
                return setProblemReport(NO_PROBLEM);
            case 64:
                this.insertPosition = getLastModifierPosition();
                this.insert = getProgramFactory().createVolatile();
                return setProblemReport(NO_PROBLEM);
            case 256:
                this.insertPosition = getLastModifierPosition();
                this.insert = getProgramFactory().createNative();
                return setProblemReport(NO_PROBLEM);
        }
        throw new IllegalArgumentException("Unsupported modifier code " + this.modifier);
    }

    public void transform() {
        super.transform();
        if (this.remove != null)
            detach(this.remove);
        if (this.insert != null)
            attach(this.insert, this.decl, this.insertPosition);
    }

    public Modifier getDetached() {
        return this.remove;
    }

    public Modifier getAttached() {
        return this.insert;
    }
}
