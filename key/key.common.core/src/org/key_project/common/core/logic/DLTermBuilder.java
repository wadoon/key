package org.key_project.common.core.logic;

import org.key_project.common.core.logic.op.Function;

public interface DLTermBuilder<T extends DLTerm<? extends DLVisitor<T>>> {

    T func(Function bool_true);

}
