FROM haskell:9.8

RUN useradd -ms /bin/bash agda && \
    echo "agda ALL=(ALL) NOPASSWD:ALL" >> /etc/sudoers

USER agda
WORKDIR /home/agda

# the guarded-pi-ccs development is in agda 2.6.4
RUN cabal update && \
    cabal install Agda-2.6.4

# cubical v0.6 is compatible with agda 2.6.4
RUN git clone https://github.com/agda/cubical /home/agda/cubical && \
    cd /home/agda/cubical && \
    git checkout v0.6

# register agda libraries
# for agda 2.6.4, AGDA_DIR is ~/.agda
RUN mkdir -p /home/agda/.agda && \
    echo "/home/agda/cubical/cubical.agda-lib" > .agda/libraries && \
    echo "cubical" > /home/agda/.agda/defaults
