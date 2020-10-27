package recoder.abstraction;

import recoder.service.ProgramModelInfo;

import java.util.List;

public interface TypeParameter extends ClassType {
    String getParameterName();

    int getBoundCount();

    String getBoundName(int paramInt);

    List<? extends TypeArgument> getBoundTypeArguments(int paramInt);

    ClassType getContainingClassType();

    class EqualsImplementor {
        public static boolean equals(TypeParameter t1, Object o) {
            if (t1 == o)
                return true;
            if (!(o instanceof TypeParameter))
                return false;
            TypeParameter t2 = (TypeParameter) o;
            ClassType c1 = t1.getContainingClassType();
            ClassType c2 = t2.getContainingClassType();
            if (c1 == null || c2 == null)
                return false;
            if (c1 == c2)
                return false;
            ProgramModelInfo pmi = c1.getProgramModelInfo();
            if (pmi.isSubtype(c1, c2)) {
                List<ClassType> tl = c1.getSupertypes();
                for (int i = 0, s = tl.size(); i < s; i++) {
                    ClassType superCT = tl.get(i);
                    if (superCT.getTypeParameters() != null)
                        if (superCT instanceof ParameterizedType) {
                            TypeParameter tryUpwards = null;
                            int ridx = -1;
                            List<? extends TypeArgument> rl = ((ParameterizedType) superCT).getTypeArgs();
                            for (int j = 0; j < rl.size(); j++) {
                                TypeArgument ta = rl.get(j);
                                if (ta.getTypeName().equals(t1.getName())) {
                                    ridx = j;
                                    break;
                                }
                            }
                            if (ridx != -1) {
                                tryUpwards = superCT.getTypeParameters().get(ridx);
                                if (equals(tryUpwards, t2))
                                    return true;
                            }
                        }
                }
            } else if (pmi.isSubtype(c2, c1)) {
                return equals((TypeParameter) o, t1);
            }
            return false;
        }
    }
}
