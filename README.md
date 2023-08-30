Lean for the Curious Mathematician 2023
=======================================
Düsseldorf, 4-8 Sep. 2023

This repository contains the exercises for the LftCM2023 workshop. It is based on
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/).
(see also its [Github Repo](https://github.com/leanprover-community/mathematics_in_lean))

The workshops website: [LftCM2023 webiste](https://lftcm2023.github.io/)


## To use this repository on your computer

Do the following:

1. Install Lean 4 and VS Code following
   these [instructions](https://leanprover-community.github.io/get_started.html).

2. Make sure you have [git](https://git-scm.com/) installed.

3. Follow these [instructions](https://leanprover-community.github.io/install/project.html#working-on-an-existing-project)
   to fetch the `lftcm2023` repository and open it up in VS Code.

4. Each section in the textbook has an associated Lean file with examples and exercises.
   You can find them in the folder `LftCM`, organized by chapter.
   We strongly recommend making a copy of that folder and experimenting and doing the
   exercises in that copy.
   This leaves the originals intact, and it also makes it easier to update the repository as it changes (see below).
   You can call the copy `my_files` or whatever you want and use it to create
   your own Lean files as well.

At that point, you can open the textbook in a side panel in VS Code as follows:

1. Type `ctrl-shift-P` (`command-shift-P` in macOS).

2. Type `Lean 4: Open Documentation View` in the bar that appears, and then
  press return. (You can press return to select it as soon as it is highlighted
  in the menu.)

3. In the window that opens, click on `Open documentation of current project`.

This repository is still a work in progress.
You can update the repository by typing `git pull`
followed by `lake exe cache get` inside the `lftcm2023` folder.
(This assumes that you have not changed the contents of the `LftCM` folder,
which is why we suggested making a copy.)
