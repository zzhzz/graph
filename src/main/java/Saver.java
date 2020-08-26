import org.javatuples.Pair;

import java.io.File;
import java.io.FileWriter;
import java.util.List;
import java.util.Arrays;
import java.util.ArrayList;
import java.util.stream.Collectors;

public class Saver {

	static String path;
	static List<String> nodes = new ArrayList<>();
	static List<Pair<Integer, Integer>> edges = new ArrayList<>();

	static void setPath(String save_path) {
		path = save_path;
	}
	static void clear() {
		nodes.clear();
		edges.clear();
	}
	static void save() {
		File node_file = new File(path + ".nodelist");
		File edge_file = new File(path + ".edgelist");
		FileWriter writer = null;
		try {
			writer = new FileWriter(node_file);
			for(String node : nodes){
				writer.write(node + "\n");
			}
			writer.close();
			writer = new FileWriter(edge_file);
			for(Pair<Integer, Integer> edge : edges) {
				writer.write(edge.getValue0() + " " + edge.getValue1() + " 1\n");
				writer.write(edge.getValue1() + " " + edge.getValue0() + " -1\n");
			}
			writer.close();
		} catch (Exception e) {
			e.printStackTrace();
		}

	}

	static void addGraph(List<String> nds, List<Pair<Integer, Integer>> egs) {
		int prefix = nodes.size();
		nodes.addAll(nds);
		edges.addAll(
			egs.stream()
			.map(p -> Pair.with(p.getValue0() + prefix, p.getValue1() + prefix))
			.collect(Collectors.toList())
	    );
	}
}
