/*
 * Algorithm 3.26: Synthesis of Third-Normal-Form Relations 
 *                  With a Lossless Join and Dependency Preservation.
 *
 * INPUT: A relation R and a set F of functional dependencies that hold for R.
 *
 * OUTPUT: A decomposition of R into a collection of relations, each of which is
 * in 3NF. The decomposition has the lossless-join and dependency-preservation
 * properties.
 *
 * METHOD: Perform the following steps:
 * 1. Find a minimal basis for F, say G.
 * 2. Partition the the functional dependencies in G according to their left hand sides 
 *    (so two dependencies X→A and X→B with the same left hand sides will be in the same partition). 
 *    Merge each partition into aco single FD using the combining rule (so X→A and X→B would become X→AB). 
 *    For each rule X→Y that results from merging the rules of a partition, use XY as the schema of one of the relations in the decomposition. 
 * 3. If none of the relation schemas from Step 2 is a superkey for R, add another relation whose schema is a key for R.
 * 4. If the set of the attributes of one table in the decomposition is a subset of the attributes of a different output table
 *    it should be deleted from the decomposition.
 */

import java.util.Arrays;
import java.util.ArrayList;
import java.io.BufferedReader;
import java.io.FileReader;
import java.util.HashSet;
import java.io.IOException;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The ModifiedSynthesis class is
 * created to carry out the synthesis
 * of Third Normal Form Relations
 * that have both the lossless join
 * and dependency presevation properties.
 */

public class ModifiedSynthesis {

    // an array containing left hand side
    // and right hand side of a functional dependency (FD)
    static String[] items;
    // an array of string numbers found
    // in left hand side of functional dependency (FD)
    static String[] lhs;
    // an array of string numbers found
    // in right hand side of functional dependency (FD)
    static String[] rhs;

    // ArrayList of sets of numbers for left hand side
    // set contains unique attributes in left hand side
    static ArrayList<HashSet<Integer>> leftSide;
    // ArrayList of sets of numbers for right hand side
    // set contains unique attributes in right hand side
    static ArrayList<HashSet<Integer>> rightSide;

    // Set that contains all unique attributes in our relation
    static HashSet<Integer> num;
    static int max;

    // Set that contains unique attributes in left hand side
    static HashSet<Integer> numsFromLeftSide;
    // Set that contains unique attributes in right hand side
    static HashSet<Integer> numsFromRightSide;

    // Regular expression intended for
    // left hand side/right hand side of FD
    static String REGEX = "[\\d,]+";
    // Use Pattern and Matcher to find strings that match the specified regular
    // expression
    static Pattern pat;
    static Matcher match;

    public static void main(String args[]) {

        // Check that we get exactly one argument to the command on terminal
        if (args.length < 1 || args.length > 1) {
            endProgram();
        }
        // Save textfile name
        String txtFile = args[0];

        // Initialize predefined variables above main method
        num = new HashSet<Integer>();
        leftSide = new ArrayList<HashSet<Integer>>();
        rightSide = new ArrayList<HashSet<Integer>>();

        // Create a Pattern object for this specified REGEX
        pat = Pattern.compile(REGEX);

        try {
            // Create a Buffered Reader for reading textfile
            BufferedReader in = new BufferedReader(new FileReader(txtFile));

            // Read in line by line in the textfile
            for (String line = in.readLine(); line != null; line = in.readLine()) {
                // Split each line by semicolon
                // Capture left hand side and right hand side
                items = line.trim().split(";");

                // Check that we have exactly two strings in items array
                if (items.length != 2) {
                    endProgram();
                }

                // Initialize predefined variables for use
                numsFromLeftSide = new HashSet<Integer>();
                numsFromRightSide = new HashSet<Integer>();

                // Create Matcher object in each iteration
                for (String item : items) {
                    // Match pattern with string in item
                    match = pat.matcher(item);
                    // if string do not conform to the format
                    if (!match.matches()) {
                        endProgram();
                    }
                }

                // Split left hand side by comma if there is comma
                lhs = items[0].split(",");
                for (String num : lhs) {
                    // Add number into LHS set
                    numsFromLeftSide.add(Integer.valueOf(num));
                }

                // Split right hand side by comma if there is comma
                rhs = items[1].split(",");
                for (String num : rhs) {
                    // Add number into RHS set
                    numsFromRightSide.add(Integer.valueOf(num));
                }

                // Add LHS set to LHS array list
                leftSide.add(numsFromLeftSide);
                // Add RHS set to RHS array list
                rightSide.add(numsFromRightSide);
            }

            // Add each set from LHS to the num set
            for (HashSet<Integer> s : leftSide) {
                num.addAll(s);
            }

            // Add each set from RHS to the num set
            for (HashSet<Integer> s : rightSide) {
                num.addAll(s);
            }

        } catch (IOException e) {
            System.out.println("ERROR!");
        }

        int max = num.size();
        // finding out the size of the initial relation
        for (Integer i : num) {
            if (max < i) {
                max = i;
            }
        }
        // fix initial relation so numbers not in fds are included
        for (int i = 1; i <= max; i++) {
            num.add(i);
        }

        int numAttributes = num.size();
        // successfully created inital relations

        // Checking for the number of attributes
        // System.out.println("Size of set: " + numAttributes);

        // Create a set representing the initial relation
        HashSet<Integer> initRelation = new HashSet<Integer>();
        // Populate the initRelation set
        for (int i = 1; i <= numAttributes; i++) {
            initRelation.add(i);
        }

        // Create an array list that will store the decomposed relations
        ArrayList<HashSet<Integer>> relations = new ArrayList<HashSet<Integer>>();
        // Initially, this array list contains the starting relation
        relations.add(initRelation);

        // Decompose the initial relation
        relations = makesRInto3NF();

        // Print out the decomposed relations
        // or if initial relation is already in 3NF, print it out
        printRelations(relations);
    }

    /**
     * The printRelations method displays
     * the provided relations line by line.
     * Each line (relation) is comprised of integers
     * representing relation attributes.
     * Integers are delimited by comma.
     * 
     * @param relations array list of sets of integers
     */
    private static void printRelations(ArrayList<HashSet<Integer>> relations) {
        // Iterate through each relation
        for (HashSet<Integer> s : relations) {
            // Create an array to contain numbers
            int[] nums = new int[s.size()];
            // Save numbers in set into array
            int i = 0;
            for (Integer n : s) {
                nums[i++] = n;
            }
            // Sort the number array
            Arrays.sort(nums);
            // Display numbers one by one, separated by comma
            for (int pos = 0; pos < nums.length; pos++) {
                System.out.print(nums[pos]);
                // if we have not reached the last number yet
                if (pos != nums.length - 1) {
                    // print out comma after the number
                    System.out.print(",");
                }
            }
            // Print each relation on its own line
            System.out.println();
        }
    }

    /**
     * The makesRInto3NF method adds
     * attributes found from LHS and RHS
     * to form a relation.
     * It also saves the key that is found
     * among the functional dependencies
     * as a relation, if appropriate.
     * 
     * @return output the array list of set of attributes
     */
    private static ArrayList<HashSet<Integer>> makesRInto3NF() {

        // find minimal basis that gives all attributes
        // returns minimal size
        FindMinBasis();

        // Revoke method to partition the FDs
        // and merge FDs in the same partition together
        partitionMergeFDs();

        // Create output array list that contains newly-formed relations
        ArrayList<HashSet<Integer>> output = new ArrayList<HashSet<Integer>>();

        // Create a copy of leftSide array list
        ArrayList<HashSet<Integer>> copyLeftSide = new ArrayList<HashSet<Integer>>(leftSide);
        // Create a copy of rightSide array list
        ArrayList<HashSet<Integer>> copyRightSide = new ArrayList<HashSet<Integer>>(rightSide);

        // for each set in the leftSide
        for (int i = 0; i < copyLeftSide.size(); i++) {

            // create a set to store attributes
            HashSet<Integer> insert = new HashSet<Integer>();

            // add attributes from LHS of the ith relation
            insert.addAll(copyLeftSide.get(i));
            // add attributes from RHS of the ith relation
            insert.addAll(copyRightSide.get(i));

            // add the newly-formed set into list
            output.add(insert);
        }

        // Check if LHS of any FD is a superkey
        HashSet<Integer> checkForKey = hasSuperKey(output);
        // if a key is found (we do not run into null value)
        if (checkForKey != null) {
            // add that set of attributes (key)
            output.add(checkForKey);
        }

        // for each set in the leftSide
        for (int i = output.size() - 1; i >= 0; i--) {
            // boolean flag to detect a relation is a subrelation
            boolean subrel = false;

            // for each set in output list
            for (int j = 0; j < output.size(); j++) {
                // if any of these sets contain the currently-formed set
                if (i != j && output.get(j).containsAll(output.get(i))) {
                    // set subrel flag to be true
                    subrel = true;
                    // end for loop
                    break;
                }
            }

            // if a subrelation is found
            if (subrel) {
                // if relation is not a subrelation
                // add the newly-formed set into list
                output.remove(i);
            }

        }

        return output;
    }

    /**
     * The endProgram method displays a message
     * to the user in cases where
     * the text file is not given on command line
     * or the text file is in wrong format.
     * The method ends the program in these scenarios.
     */
    public static void endProgram() {
        System.out.println("ERROR!");
        System.exit(0);
    }

    /*
     * The partitionMergeFDs checks if any singleton from
     * left hand side of FD matches.
     * If any matches are found, add the left hand side and
     * right hand sides of each FD to
     * the same partition.
     */
    public static void partitionMergeFDs() {
        // first FD
        // start at index i
        for (int i = 0; i < leftSide.size(); i++) {
            // second FD
            // start at the next index i + 1
            int j = i + 1;
            while (j < leftSide.size()) {
                // if first FD share the same elements as second FD
                if ((leftSide.get(i)).equals(leftSide.get(j))) {

                    // add the right side of second FD to first FD
                    rightSide.get(i).addAll(rightSide.get(j));

                    // delete the merged FD
                    leftSide.remove(j);
                    rightSide.remove(j);
                } else {
                    j++;
                }
            }
        }

    }

    /**
     * The hasSuperKey method is created to find
     * the super key using the given functional
     * dependencies available in the text file.
     * 
     * @param output array list of sets of attributes
     * @return set of attributes (superkey)
     */
    public static HashSet<Integer> hasSuperKey(ArrayList<HashSet<Integer>> output) {
        // Check if the closure contains all the attributes in the relation
        // The number of unique attributes is found from num.size()
        // Check if closure.size() == num.size()
        boolean hasSuperKey = false;
        for (int i = 0; i < leftSide.size(); i++) {
            if (FindClosure(output.get(i), i).size() == num.size()) { // flagged
                hasSuperKey = true;
            }
        }

        // if no superkey, return a superkey
        if (!hasSuperKey) {
            int closest = 0;
            int indexClosest = 0;
            HashSet<Integer> key = new HashSet<Integer>();
            // Add a relation whose schema is a key for R
            for (int i = 0; i < leftSide.size(); i++) {
                // Try to find a relation whose closure contains all the unique attributes
                HashSet<Integer> candidateKey = FindClosure(leftSide.get(i));
                // If closure calculated without FDs equals num.size(), all the number of
                // attributes, add the set to something...

                if (closest < candidateKey.size()) {
                    key = leftSide.get(i);
                    closest = candidateKey.size();
                    indexClosest = i;
                }

            }

            HashSet<Integer> keyClosure = FindClosure(leftSide.get(indexClosest));
            HashSet<Integer> numCopy = new HashSet<Integer>(num);
            key.addAll(leftSide.get(indexClosest));
            numCopy.removeAll(keyClosure);
            key.addAll(numCopy);

            // the correct key/candidate key
            return key;
        }
        return null;
    }

    /**
     * The FindMinBasis method will
     * look for a set of functional
     * dependencies in which
     * 1. All FD's have singleton right sides
     * 2. If any FD is removed, the result is
     * no longer a basis
     * 3. If for any FD in basis we remove one
     * or more attributes from LHS of F, the result
     * is no longer a basis.
     */
    public static void FindMinBasis() {
        // makes sure all fds ahave singleton right sides
        applySplittingRule();

        int loop = leftSide.size() - 1;
        // check if all the fds are actually needed
        for (int i = loop; i >= 0; i--) {

            // find elements that can directly be found with that FD
            HashSet<Integer> union = new HashSet<Integer>();
            union.addAll(leftSide.get(i));
            union.addAll(rightSide.get(i));
            // calculate closure with FD
            HashSet<Integer> withFD = FindClosure(union, i);
            // calculate closure without that FD
            HashSet<Integer> withoutFD = FindClosure(leftSide.get(i), i);
            // if they are NOT the same, add that FD to minimal basis
            if (withoutFD.equals(withFD)) {
                leftSide.remove(i);
                rightSide.remove(i);
            }
        }

        // makes sure all elements on leftSide are needed
        checksForUnnecessaryElements();

    }

    /**
     * The checksForUnnecessaryElements method
     * verifies whether all the functional
     * dependencies are needed.
     */
    private static void checksForUnnecessaryElements() {
        for (int i = 0; i < leftSide.size(); i++) {
            if (leftSide.get(i).size() > 1) {
                for (Integer j : leftSide.get(i)) {
                    HashSet<Integer> withE = FindClosure(leftSide.get(i));
                    HashSet<Integer> difference = new HashSet<Integer>(leftSide.get(i));
                    difference.remove(j);
                    HashSet<Integer> withoutE = FindClosure(difference);
                    if (withoutE.containsAll(withE)) {
                        leftSide.set(i, difference);
                    }
                }
            }
        }
    }

    /**
     * The applySplittingRule method
     * will take a functional dependency
     * of this form: X -> AB, and break it
     * into two FD's: X -> A and X -> B.
     */
    private static void applySplittingRule() {
        // find the number of functional dependencies
        int fdCount = leftSide.size();
        // array list of attributes to be removed
        ArrayList<Integer> indexToBeDeleted = new ArrayList<Integer>();
        // for each functional dependency
        for (int i = 0; i < fdCount; i++) {
            // if RHS of FD has more than one attribute
            if (rightSide.get(i).size() > 1) {
                // for each attribute on RHS
                for (Integer j : rightSide.get(i)) {
                    // Add what is already on LHS
                    leftSide.add(leftSide.get(i));
                    // Add new RHS
                    HashSet<Integer> toBeAdded = new HashSet<Integer>();
                    toBeAdded.add(j);
                    rightSide.add(new HashSet<>(toBeAdded));
                }
                // Save index of the old FD
                indexToBeDeleted.add(i);
            }
        }

        // delete split fd from greatest index to least to avoid index errors
        for (int i = indexToBeDeleted.size() - 1; i >= 0; i--) {

            leftSide.remove((int) indexToBeDeleted.get(i));
            rightSide.remove((int) indexToBeDeleted.get(i));
        }

    }

    /**
     * The FindClosure method will
     * add the right side of FD if
     * left side of FD is in the closure
     * and right side is not.
     * 
     * @param leftAtt a set of left side attributes
     * @return a set of attributes obtained in closure
     */
    public static HashSet<Integer> FindClosure(HashSet<Integer> leftAtt) {
        // closure = x (leftAtt), olcClosure = empty set
        HashSet<Integer> closure = new HashSet<Integer>(leftAtt);
        HashSet<Integer> oldClosure = new HashSet<Integer>();
        // while x_old != x
        while (closure.size() != oldClosure.size()) {
            // set x_old to x
            oldClosure = new HashSet<Integer>(closure);

            // for each FD,
            for (int i = 0; i < leftSide.size(); i++) {
                // check whether the LHS attributes are in closure, but RHS attributes are not
                if (closure.containsAll(leftSide.get(i))) {
                    // Add RHS attributes into closure
                    closure.addAll(rightSide.get(i));
                }
            }
        }
        return closure;
    }

    /**
     * The second FindClosure method does the same
     * operation as the first FindClosure method
     * It is an overloaded method with two parameters.
     * 
     * @param leftAtt a set of left side attributes
     * @param index   position of the FD in the array list
     * @return a set of attributes in the closure
     */
    public static HashSet<Integer> FindClosure(HashSet<Integer> leftAtt, Integer index) {
        // closure = x (leftAtt), olcClosure = empty set
        HashSet<Integer> closure = new HashSet<Integer>(leftAtt);
        HashSet<Integer> oldClosure = new HashSet<Integer>();
        // while x_old != x
        while (closure.size() != oldClosure.size()) {
            // set x_old to x
            oldClosure = new HashSet<Integer>(closure);

            // for each FD,
            for (int i = 0; i < leftSide.size(); i++) {
                // check whether the LHS attributes are in closure, but RHS attributes are not
                if ((i != index) && closure.containsAll(leftSide.get(i))) {
                    // Add RHS attributes into closure
                    closure.addAll(rightSide.get(i));
                }
            }
        }
        return closure;
    }
}
