package recoder.abstraction;

import java.util.List;

public interface Field extends Variable, Member {
    List<? extends TypeArgument> getTypeArguments();
}
