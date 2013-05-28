package se.gu.svanefalk.testgeneration.core.concurrency.capsules;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class CapsuleController<T extends ICapsule> {

    /**
     * Global thread pool for dispatching other capsules.
     */
    CapsuleExecutor capsuleExecutor = CapsuleExecutor.getInstance();

    /**
     * Capsules controlled by this instance.
     */
    private final Map<T, LaunchContainer> childCapsules = new HashMap<>();

    public void addChild(T capsule) {
        capsule.addController(this);
        childCapsules.put(capsule, new LaunchContainer(capsule));
    }

    public void stopChild(T capsule) {
        childCapsules.get(capsule).stop();
        childCapsules.remove(capsule);
    }

    public void stopChildren() {
        for (LaunchContainer capsule : childCapsules.values()) {
            capsule.stop();
        }
    }

    public void executeAndWait() {
        capsuleExecutor.executeCapsulesAndWait(childCapsules.values());
    }

    public Collection<T> getCapsules() {
        return childCapsules.keySet();
    }
}
