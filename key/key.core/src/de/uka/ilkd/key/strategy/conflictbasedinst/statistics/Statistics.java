package de.uka.ilkd.key.strategy.conflictbasedinst.statistics;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;

public class Statistics implements Serializable {

    /**
     *
     */
    private static final long serialVersionUID = 2998170572795789151L;

    private Statistics stats = null;

    private static final String STATISTICS_FILENAME = "statistics.obj";
    private static final boolean STATISTICS_ENABLED = true;

    private Statistics() {

    }

    private Statistics stats() throws ClassNotFoundException, IOException {
        if(stats != null) return stats;
        stats = read();
        return stats;
    }

    private void save() {
        try {
            File file = new File(STATISTICS_FILENAME);
            if(file.exists()) file.delete();
            file.createNewFile();
            FileOutputStream fos = new FileOutputStream(file);
            ObjectOutputStream oos = new ObjectOutputStream(fos);
            oos.writeObject(this);
            oos.close();
        }
        catch (FileNotFoundException e) {
            System.out.println("File does not exist, this should not be possible.");
            e.printStackTrace();
        }
        catch (IOException e) {
            System.out.println("Could not write statistics file.");
            e.printStackTrace();
        }
    }

    private Statistics read() throws IOException, ClassNotFoundException {
        File file = new File(STATISTICS_FILENAME);
        FileInputStream fis = new FileInputStream(file);
        ObjectInputStream ois = new ObjectInputStream(fis);
        Statistics stats = (Statistics)ois.readObject();
        ois.close();
        return stats;
    }

}
