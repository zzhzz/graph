import org.javatuples.Pair;

import java.io.File;
import java.io.FileWriter;
import java.util.List;

public class Saver {

    static String path;
    static Integer part_number = 0;

    static void setPath(String save_path) {
        path = save_path;
    }

    static void addGraph(List<String> nodes, List<Pair<Integer, Integer>> edges) {
        File node_file = new File(String.valueOf(part_number) + ".nodelist");
        File edge_file = new File(String.valueOf(part_number) + ".edgelist");
        FileWriter writer = null;
        try {
            writer = new FileWriter(node_file);
            for(String node : nodes){
                writer.write(node + "\n");
            }
            writer.close();
            writer = new FileWriter(edge_file);
            for(Pair<Integer, Integer> edge : edges) {
                writer.write(edge.getValue0() + " " + edge.getValue1() + "\n");
            }
            writer.close();
            part_number++;
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}
