package recoder.service;

import java.util.EventObject;
import java.util.List;

public class ChangeHistoryEvent extends EventObject {
    private static final long serialVersionUID = -5303809748311641541L;

    private final List<TreeChange> changeList;

    ChangeHistoryEvent(ChangeHistory source, List<TreeChange> changeList) {
        super(source);
        this.changeList = changeList;
    }

    public List<TreeChange> getChanges() {
        return this.changeList;
    }

    public String toString() {
        StringBuffer res = new StringBuffer();
        for (int i = 0; i < this.changeList.size(); i++) {
            res.append(this.changeList.get(i).toString());
            res.append("\n");
        }
        return res.toString();
    }
}
