
Needs @ "PacletManager`";

Block[
  {
    $projectDirectory = DirectoryName[ $InputFileName /. "" :> NotebookFileName[] ],
    $project = "BayesianInference"
  },
  PackPaclet @ FileNameJoin[{ $projectDirectory, $project}]
]
