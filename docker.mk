REGISTRY := "ams.vultrcr.com/lthms"
IMAGE := "www/soap.coffee"

.PHONY: build-docker
build-docker:
	$(MAKE) -f makefile gen
	docker build \
		-f ./build.Dockerfile \
		--target soap.coffee \
		-t $(IMAGE):latest \
		.

.PHONY: push-staging
push-staging:
	docker tag $(IMAGE):latest $(REGISTRY)/$(IMAGE):staging
	docker push $(REGISTRY)/$(IMAGE):staging

.PHONY: push
push:
	docker tag $(IMAGE):latest $(REGISTRY)/$(IMAGE):live
	docker push $(REGISTRY)/$(IMAGE):live

.PHONY: static
static: build-docker
	docker create --name soap-coffee-build $(IMAGE):latest
	docker cp soap-coffee-build:/bin/soap.coffee .
	docker rm -f soap-coffee-build
