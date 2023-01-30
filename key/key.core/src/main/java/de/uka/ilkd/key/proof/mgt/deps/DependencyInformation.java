package de.uka.ilkd.key.proof.mgt.deps;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

/**
 * All dependency information for a given folder
 */
public class DependencyInformation {
    /**
     * The folder name associated with this information
     */
    private final String folderName;
    /**
     * Dependencies for each Java file in the folder
     */
    private final Map<String, FileDependencyInformation> fileInfos;

    public DependencyInformation(String folderName, Map<String, FileDependencyInformation> fileInfos) {
        this.folderName = folderName;
        this.fileInfos = fileInfos;
    }

    public Set<Map.Entry<String, FileDependencyInformation>> getFileInformationEntries() {
        return fileInfos.entrySet();
    }

    public String getFolderName() {
        return folderName;
    }

    public Collection<FileDependencyInformation> getFileDependencyInfos() {
        return fileInfos.values();
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (FileDependencyInformation fdi : fileInfos.values()) {
            sb.append(fdi.toString());
            sb.append(", ");
        }
        return folderName + ": " + sb.toString();
    }
}
