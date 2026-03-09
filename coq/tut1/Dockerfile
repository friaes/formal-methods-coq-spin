# Dockerfile
FROM coqorg/coq:latest

# Install dependencies for VSCoq
RUN opam update
RUN opam install -y vscoq-language-server

# Set the working directory
WORKDIR /

# Keep the container running
ENTRYPOINT ["sleep", "infinity"]
