package recoder.abstraction;

import java.util.List;

public interface TypeArgument {
    WildcardMode getWildcardMode();

    String getTypeName();

    List<? extends TypeArgument> getTypeArguments();

    enum WildcardMode {
        None, Any, Extends, Super
    }
}
